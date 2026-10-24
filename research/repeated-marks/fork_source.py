"""Mechanical fork of the tainted part of Collet's source step.

For every module of Collet's tree that declares a tainted declaration of the NF-step closure
(fork_closure.tsv, written by Scratch/ForkAnalysis2.lean), emit a module
`Submissions/repeated_marks_20261024/Fork/<same path>.lean` that
  * imports Collet's original module (for all untainted declarations) and the forks of its
    imports;
  * keeps the module's namespace/section/open/variable/notation structure verbatim;
  * re-declares only the tainted declarations, renamed `<name>_rm` in the same namespace;
  * re-points every reference to a tainted declaration to its `_rm` copy.
Semantic replacements (the gain, the cutoff, the gaps, the validity predicate) are made by hand
afterwards; the seeds themselves are never renamed.

usage: python3 fork_source.py fork_closure.tsv fork_tainted_all.txt OUTROOT
"""
import os, re, sys, collections

CROOT = '/home/user/QuasiRiemannTracker/submissions/hailey-collet-1252270103/src'
CPKG = 'Submissions.hailey_collet_1252270103'
PKG = 'Submissions.repeated_marks_20261024'
SEEDS = {'QRH.Record1252270103Source.High.gain', 'QRH.Record1252270103Source.High.cutoff',
         'Record1252270103Finite.SourceValid'}
SUFFIX = '_rm'
DECL_KW = r'(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(private|protected)\s+)?(?:noncomputable\s+)?(?:nonrec\s+)?'
                  + DECL_KW + r'\s+([^\s:({\[⦃]+)')
TOP = re.compile(r'^(?:@\[|/--|/-|theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom|'
                 r'private|protected|noncomputable|nonrec|namespace|section|end|open|variable|universe|'
                 r'local|scoped|set_option|attribute|include|omit|#|import|mutual|export|example|unseal|'
                 r'macro|syntax|notation|infix|postfix|prefix|deriving)')
IDENT = re.compile(r"(?<![A-Za-z_0-9'.])((?:[A-Za-z_][A-Za-z_0-9'!?]*\.)*[A-Za-z_][A-Za-z_0-9'!?]*)")


def module_path(m):
    return os.path.join(CROOT, m.replace('.', '/') + '.lean')


def split_commands(text):
    """Split a Lean file into top-level chunks starting at column-0 command keywords."""
    lines = text.split('\n')
    chunks, cur = [], []
    in_comment = 0
    for line in lines:
        starts = (not in_comment) and bool(TOP.match(line)) and not line.startswith(' ')
        if starts and cur:
            chunks.append('\n'.join(cur))
            cur = []
        cur.append(line)
        in_comment += line.count('/-') - line.count('-/')
        in_comment = max(in_comment, 0)
    if cur:
        chunks.append('\n'.join(cur))
    return chunks


def attach(chunks):
    """Glue doc comments, attributes and `... in` prefixes to the declaration they precede."""
    out, pending = [], []
    for c in chunks:
        first = c.split('\n', 1)[0]
        is_prefix = (first.startswith('/--') or (first.startswith('@[') and DECL.match(c) is None)
                     or re.match(r'^(include|omit|set_option)\b.*\bin\s*$', first))
        if is_prefix:
            pending.append(c)
            continue
        out.append('\n'.join(pending + [c]))
        pending = []
    if pending:
        out.append('\n'.join(pending))
    return out


def decl_info(chunk):
    for line in chunk.split('\n'):
        if line.startswith('/--') or line.startswith('@[') and DECL.match(line) is None:
            continue
        if re.match(r'^(include|omit|set_option)\b.*\bin\s*$', line):
            continue
        m = DECL.match(line)
        return (m.group(2), m.group(1)) if m else None
    return None


GAIN_REP = 'QRH.RepeatedMarks.Source.gainRep 8'


def rename_refs(text, short_map, in_high=False):
    """Re-point tainted references to their `_rm` copies; the HIGH gain becomes `gainRep 8`."""
    def rep(m):
        tok = m.group(1)
        if tok in ('High.gain', 'QRH.Record1252270103Source.High.gain') or (in_high and tok == 'gain'):
            return GAIN_REP
        parts = tok.split('.')
        if parts[-1] in short_map:
            parts[-1] = parts[-1] + SUFFIX
            return '.'.join(parts)
        return tok
    return IDENT.sub(rep, text)


def main():
    tsv, allf, out = sys.argv[1], sys.argv[2], sys.argv[3]
    fork = collections.OrderedDict()
    for line in open(tsv):
        line = line.rstrip('\n')
        if not line:
            continue
        mod, names = line.split('\t')
        fork[mod] = [n for n in names.split() if n not in SEEDS]
    forked_full = {n for ns in fork.values() for n in ns}
    short_map = collections.defaultdict(set)
    for n in forked_full:
        short_map[n.split('.')[-1]].add(n)
    stats = []
    for mod, names in fork.items():
        text = open(module_path(mod)).read()
        chunks = attach(split_commands(text))
        keep, ns_stack = [], []
        imports = [f'import {mod}']
        kept = 0
        for c in chunks:
            first = c.split('\n', 1)[0]
            if first.startswith('import '):
                for l in c.split('\n'):
                    if l.startswith('import '):
                        tgt = l.split()[1]
                        if tgt in fork:
                            imports.append(f'import {PKG}.Fork.{tgt[len(CPKG) + 1:]}')
                continue
            m = re.match(r'^namespace\s+(\S+)', first)
            if m:
                ns_stack.append(m.group(1)); keep.append(c); continue
            m = re.match(r'^end\s+(\S+)', first)
            if m and ns_stack and ns_stack[-1] == m.group(1):
                ns_stack.pop(); keep.append(c); continue
            if first.startswith('#'):
                continue
            info = decl_info(c)
            if info is None:
                # open / variable / section / notation / local instance ...; a named local instance
                # is also a global constant, which would clash with Collet's copy
                c = re.sub(r'^((?:local|scoped)\s+instance\s+)([A-Za-z_][A-Za-z_0-9]*)(\s|:)',
                           r'\1\2' + SUFFIX + r'\3', c, count=1)
                keep.append(c)
                continue
            name, vis = info
            full = '.'.join(ns_stack + [name])
            in_high = bool(ns_stack) and ns_stack[-1].startswith('QRH.Record1252270103Source.High')
            if vis == 'private':
                keep.append(rename_refs(c, short_map, in_high))
                continue
            if full in forked_full or (name.startswith('_root_.') and name[7:] in forked_full):
                kept += 1
                keep.append(rename_refs(c, short_map, in_high))
                continue
            # untainted declaration: provided by Collet's module
        body = '\n'.join(keep)
        rel = mod[len(CPKG) + 1:]
        path = os.path.join(out, 'Fork', rel.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(path), exist_ok=True)
        hdr = (f'/- Repeated marks: fork of {rel} (Hailey Collet, Apache-2.0; inherited notices retained).\n'
               f'Only the declarations whose statement depends on the HIGH gain, the uniform detector\n'
               f'cutoff or the source validity are restated, renamed `*{SUFFIX}`. -/\n')
        open(path, 'w').write(hdr + '\n'.join(dict.fromkeys(imports)) + '\n' + body + '\n')
        stats.append((rel, len(names), kept))
    for rel, n, k in stats:
        flag = '' if n == k else f'   <-- expected {n}'
        print(f'{rel}: kept {k}{flag}')
    print(len(stats), 'modules')


if __name__ == '__main__':
    main()
