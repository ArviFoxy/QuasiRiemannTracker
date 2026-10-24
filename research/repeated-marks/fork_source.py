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

usage: python3 fork_source.py fork_closure.tsv fork_tainted_all.txt OUTROOT [ROOTS.lean]
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fork_patches import PATCHES

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
    depth = 0
    for line in chunk.split('\n'):
        if depth > 0 or line.startswith('/-'):
            depth += line.count('/-') - line.count('-/')
            depth = max(depth, 0)
            continue
        if line.startswith('@[') and DECL.match(line) is None:
            continue
        if re.match(r'^(include|omit|set_option)\b.*\bin\s*$', line):
            continue
        m = DECL.match(line)
        return (m.group(2), m.group(1)) if m else None
    return None


GAIN_REP = 'QRH.RepeatedMarks.Source.gainC'


def rename_refs(text, short_map, in_high=False):
    """Re-point tainted references to their `_rm` copies; the HIGH gain becomes `gainC`."""
    # a locally bound `gain` (a `let` or a binder) shadows the HIGH gain: such chunks name the
    # HIGH gain in full
    bare = in_high and not re.search(r'\blet\s+gain\s*:=|[({]\s*gain\s*:', text)

    def rep(m):
        tok = m.group(1)
        if tok in ('High.gain', 'QRH.Record1252270103Source.High.gain') or (bare and tok == 'gain'):
            return GAIN_REP
        if tok in ('SourceValid', 'Record1252270103Finite.SourceValid'):
            return 'QRH.RepeatedMarks.Finite.SourceValidC'
        for full, rep_ in REPLACE.items():
            if tok == full or tok == full.split('.')[-1] or full.endswith('.' + tok):
                return rep_
        parts = tok.split('.')
        if parts[-1] in short_map:
            parts[-1] = parts[-1] + SUFFIX
            return '.'.join(parts)
        return tok
    # rename in code only; comments and doc strings are kept verbatim
    out, pos = [], 0
    for m in COMMENT.finditer(text):
        out.append(IDENT.sub(rep, text[pos:m.start()]))
        out.append(m.group(0))
        pos = m.end()
    out.append(IDENT.sub(rep, text[pos:]))
    return ''.join(out)


COMMENT = re.compile(r'/-.*?-/|--[^\n]*', re.S)


# Modules replaced wholesale by hand forks: their tainted declarations are not emitted, references
# are re-pointed to `_rm` names provided by the hand-fork wrapper modules below.
HAND_MODULES = {
    f'{CPKG}.Record1252270103Source.High.ActualFiber',
    f'{CPKG}.Record1252270103Source.High.WeightedFiber',
    f'{CPKG}.Record1252270103Source.High.WeightedRows',
    f'{CPKG}.Record1252270103Source.High.SourceFields',
    f'{CPKG}.Record1252270103Source.High.ActualWeighted',
}
# Individual declarations provided (as `<name>_rm`, Collet-shaped) by hand-written wrapper modules.
HAND_NAMES = {
    'QRH.Record1252270103Source.PhysicalScalar.selectedGain',
    'QRH.Record1252270103Source.PhysicalScalar.ActualGaps',
    'QRH.Record1252270103Source.HighScalar.gainAt',
    'QRH.Record1252270103Source.HighScalar.actual_gap_gain_payment',
    'QRH.Record1252270103Source.HighScalar.gainAt_weighted_width_mono',
    'QRH.Record1252270103Source.High.actual_feedback_witness_family',
    'QRH.Record1252270103Source.High.ordinary_local_witness_family',
    # the top of the NF step is the hand-written Source/NFStep2.lean
    'QRH.Record1252270103Source.InitialRegularToTruncated.nf_truncated',
    'QRH.Record1252270103Source.InitialRegularToTruncated.actual_gaps_mono',
    'QRH.Record1252270103Source.InitialTruncated.NFTruncatedInlet',
    'QRH.Record1252270103Source.InitialTruncated.nf_physical_of_truncated',
    'QRH.Record1252270103Source.InitialTruncated.nf_step_of_truncated',
    'QRH.Record1252270103Low.HeightAnchor.NFPhysicalInlet',
    'QRH.Record1252270103Low.HeightAnchor.nf_step_of_physical',
    'QRH.Record1252270103Graph.NFStep',
    'QRH.Record1252270103Graph.parent_good_of_source_valid',
    'QRH.Record1252270103Source.PhysicalScalar.nf_actual_uniform_reserve',
    'QRH.Record1252270103Source.PhysicalScalar.some_actual_reserve',
    'QRH.Record1252270103Source.PhysicalScalar.none_actual_reserve',
    # Collet's own gain and cutoff identities: superseded by Gain/ and Source/FiberK
    'QRH.Record1252270103Source.High.gain_count_identity',
    'QRH.Record1252270103Source.High.cutoff_balance',
    'QRH.Record1252270103Source.High.cutoff_bounds',
    'QRH.Record1252270103Source.High.gain_eq_min_facets',
    'QRH.Record1252270103Source.High.gain.eq_1',
    # Collet's gain lemmas, restated for the clamped repeated-mark gain in Source/GainC.lean
    'QRH.Record1252270103Source.High.gain_mono',
    'QRH.Record1252270103Source.High.gain_le_cmax',
    'QRH.Record1252270103Source.High.gain_row_loss',
    'QRH.Record1252270103Source.High.gain_rescale',
    'QRH.Record1252270103Source.High.gain_homogeneous',
    'QRH.Record1252270103Source.High.weighted_exponent_mono',
    # branch identities of Collet's gain: false for the repeated-mark gain, and unused once the
    # lemmas above are restated
    'QRH.Record1252270103Source.High.gain_le_branch',
    'QRH.Record1252270103Source.High.gain_eq_some_branch',
    'QRH.Record1252270103Source.High.gain_slot_loss',
    'QRH.Record1252270103Source.High.common_gain_loss',
    'QRH.Record1252270103Source.High.common_gain_reserve',
    'QRH.Record1252270103Source.HighScalar.gainAt_common_reserve',
    'QRH.Record1252270103Source.HighScalar.gainAt_homogeneous',
}
# Tainted declarations replaced by existing repeated-mark declarations with a different name.
REPLACE = {
    'Record1252270103Finite.source_full_width_gates': 'QRH.RepeatedMarks.Finite.sourceC_full_width_gates',
    'QRH.Record1252270103StepScalar.nf_uniform_margin': 'QRH.RepeatedMarks.Finite.nfC_uniform_margin',
}
WRAPPER_IMPORTS = [f'{PKG}.Source.GainC', f'{PKG}.Source.CountWrappersK', f'{PKG}.Source.GainPaymentK', f'{PKG}.Source.PaymentWrappersK', f'{PKG}.Source.WitnessWrappersK',
                   f'{PKG}.Finite.SourceValid2']


def main():
    tsv, allf, out = sys.argv[1], sys.argv[2], sys.argv[3]
    roots_file = sys.argv[4] if len(sys.argv) > 4 else None
    fork = collections.OrderedDict()
    hand_names = set()
    for line in open(tsv):
        line = line.rstrip('\n')
        if not line:
            continue
        mod, names = line.split('\t')
        ns = [n for n in names.split() if n not in SEEDS]
        if mod in HAND_MODULES:
            hand_names |= set(ns)
            continue
        hand_names |= {n for n in ns if n in HAND_NAMES}
        fork[mod] = [n for n in ns if n not in HAND_NAMES and n not in REPLACE]
    fork = collections.OrderedDict((m, ns) for m, ns in fork.items() if ns)
    forked_full = {n for ns in fork.values() for n in ns} | hand_names
    short_map = collections.defaultdict(set)
    for n in forked_full:
        short_map[n.split('.')[-1]].add(n)
    # pass 1: per module, the skeleton (structural chunks and forked declarations, renamed)
    items, decl_mod, decl_text, direct = {}, {}, {}, {}
    for mod, names in fork.items():
        text = open(module_path(mod)).read()
        chunks = attach(split_commands(text))
        its, ns_stack, dimp = [], [], []
        mine = set(names)
        for c in chunks:
            first = c.split('\n', 1)[0]
            if first.startswith('import '):
                for l in c.split('\n'):
                    if l.startswith('import '):
                        dimp.append(l.split()[1])
                continue
            m = re.match(r'^namespace\s+(\S+)', first)
            if m:
                ns_stack.append(m.group(1)); its.append(('s', c)); continue
            m = re.match(r'^end\s+(\S+)', first)
            if m and ns_stack and ns_stack[-1] == m.group(1):
                ns_stack.pop(); its.append(('s', c)); continue
            if first.startswith('#'):
                continue
            info = decl_info(c)
            if info is None:
                c = re.sub(r'^((?:local|scoped)\s+instance\s+)([A-Za-z_][A-Za-z_0-9]*)(\s|:)',
                           r'\1\2' + SUFFIX + r'\3', c, count=1)
                its.append(('s', c))
                continue
            name, vis = info
            full = '.'.join(ns_stack + [name])
            in_high = bool(ns_stack) and ns_stack[-1].startswith('QRH.Record1252270103Source.High')
            if vis == 'private':
                key = f'{mod}#private#{full}'
                its.append(('d', key))
                decl_text[key] = rename_refs(c, short_map, in_high)
                decl_mod[key] = mod
                continue
            if full in mine or (name.startswith('_root_.') and name[7:] in mine):
                its.append(('d', full))
                decl_text[full] = rename_refs(c, short_map, in_high)
                decl_mod[full] = mod
        items[mod] = its
        direct[mod] = dimp
    # pass 2: keep the declarations reachable from the roots (all forked ones without roots)
    def resolve(tok, key):
        """The forked declarations a `*_rm` token in declaration `key` can denote."""
        q = tok[:-len(SUFFIX)]
        short = q.split('.')[-1]
        cands = [n for n in short_map.get(short, ()) if n in decl_text and (n == q or n.endswith('.' + q))]
        if len(cands) > 1:
            same = [n for n in cands if decl_mod[n] == decl_mod[key]]
            if same:
                return same
            ns = key.split('#')[-1].rsplit('.', 1)[0]
            pref = [n for n in cands if ns.startswith(n.rsplit('.', 1)[0])]
            if pref:
                return pref
        return cands

    def refs(key):
        out_ = set()
        for tok in set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.!?]*" + SUFFIX + r"\b", decl_text[key])):
            out_ |= set(resolve(tok, key))
        # private helpers of the same module are referenced by bare name
        for k in decl_text:
            if '#private#' in k and decl_mod[k] == decl_mod[key] and k != key:
                if re.search(r'(?<![A-Za-z_0-9.])' + re.escape(k.split('.')[-1]) + r'(?![A-Za-z_0-9])',
                             decl_text[key]):
                    out_.add(k)
        return out_
    if roots_file:
        rtxt = open(roots_file).read()
        roots = set()
        for tok in set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.!?]*" + SUFFIX + r"\b", rtxt)):
            q = tok[:-len(SUFFIX)]
            short = q.split('.')[-1]
            roots |= {n for n in short_map.get(short, ()) if n in decl_text and (n == q or n.endswith('.' + q))}
        seen, todo = set(roots), list(roots)
        while todo:
            k = todo.pop()
            for r in refs(k):
                if r not in seen:
                    seen.add(r); todo.append(r)
    else:
        seen = set(decl_text)
    emitted = {m for m in fork if any(t == 'd' and k in seen for t, k in items[m])}
    stats = []
    for mod in fork:
        if mod not in emitted:
            continue
        imports = [f'import {mod}'] + [f'import {w}' for w in WRAPPER_IMPORTS]
        for tgt in direct[mod]:
            if tgt in emitted:
                imports.append(f'import {PKG}.Fork.{tgt[len(CPKG) + 1:]}')
        body, kept = [], 0
        for t, k in items[mod]:
            if t == 's':
                body.append(k)
            elif k in seen:
                body.append(decl_text[k])
                kept += 1
                for r in refs(k):
                    rm = decl_mod[r]
                    if rm != mod:
                        imports.append(f'import {PKG}.Fork.{rm[len(CPKG) + 1:]}')
        rel = mod[len(CPKG) + 1:]
        path = os.path.join(out, 'Fork', rel.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(path), exist_ok=True)
        hdr = (f'/- Repeated marks: fork of {rel} (Hailey Collet, Apache-2.0; inherited notices retained).\n'
               f'Only the declarations whose statement depends on the HIGH gain, the uniform detector\n'
               f'cutoff or the source validity are restated, renamed `*{SUFFIX}`. -/\n')
        text = hdr + '\n'.join(dict.fromkeys(imports)) + '\n' + '\n'.join(body) + '\n'
        for old, new in PATCHES.get(rel, []):
            if text.count(old) != 1:
                raise SystemExit(f'patch for {rel} applies {text.count(old)} times:\n{old}')
            text = text.replace(old, new)
        open(path, 'w').write(text)
        stats.append((rel, len(fork[mod]), kept))
    for rel, n, k in stats:
        flag = '' if n == k else f'   (of {n})'
        print(f'{rel}: kept {k}{flag}')
    dropped = sorted(k for k in decl_text if k not in seen and '#private#' not in k)
    print(len(stats), 'modules;', len(dropped), 'unreachable declarations dropped:')
    for k in dropped:
        print('   ', k)


if __name__ == '__main__':
    main()
