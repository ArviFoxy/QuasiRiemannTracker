"""Fork Collet's generic physical return (the modules depending on `GenericArithmetic.PhysicalSchedule`)
into QRH.RepeatedMarks.Return, so that the physical schedule can drop the window guards (Lemma D).

The forked modules are Schedule, GenericFeedback, GenericScalar and PhysicalDirect/**; the final-stage
modules (FinalSchedule, FinalRows, Endpoint*) are already forked by fork_return.py into the same
namespace, and resolve the generic names to these copies through the namespace ancestors. The
intermediate stage keeps Collet's own generic modules.

Mechanical rules:
  * module `Record1252270103Return.<path>` -> `Submissions.repeated_marks_20261024.ReturnD.<path>`;
  * `namespace/end QRH.Record1252270103Return.X` -> `QRH.RepeatedMarks.Return.X`, followed by
    `open QRH.Record1252270103Return` so that Collet's unforked return names still resolve;
  * fully qualified references to forked declarations are re-pointed;
  * `open` of a namespace holding only forked declarations is re-pointed;
  * `#print axioms` lines are dropped.
Semantic edits are applied afterwards from fork_physical_patches.py.

usage: python3 fork_physical.py OUTROOT SP
(SP: the numerator cap of the physical face, at most the cap of the final physical face)
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fork_physical_patches as FP
HERE = os.path.dirname(os.path.abspath(__file__))

SRC = '/home/user/QuasiRiemannTracker/submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103'
CPKG = 'Submissions.hailey_collet_1252270103'
PKG = 'Submissions.repeated_marks_20261024'
NS_OLD, NS_NEW = 'QRH.Record1252270103Return', 'QRH.RepeatedMarks.Return'
ROOT_MOD = 'Record1252270103Return.Schedule'
# final-stage and intermediate-stage modules are not part of the generic fork
EXCLUDE = {'Record1252270103Return.FinalSchedule', 'Record1252270103Return.FinalRows',
           'Record1252270103Return.EndpointFromSources', 'Record1252270103Return.EndpointFromGlobalSources'}
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)?(?:noncomputable\s+)?(?:nonrec\s+)?"
                  r"(?:def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque)\s+([A-Za-z_][A-Za-z_0-9.'!?]*)")
HDR = ("/- Repeated marks: fork of Collet's generic physical return module {m} (Record1252270103Return,\n"
       "Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return so that the\n"
       "physical schedule applies the physical face globally (Lemma D). -/\n")


def write_if_changed(path, text):
    """Write only when the content changes, so that unchanged modules keep their build."""
    if os.path.exists(path) and open(path).read() == text:
        return
    open(path, 'w').write(text)


def all_modules():
    mods = {}
    base = os.path.join(SRC, 'Record1252270103Return')
    for d, _, fs in os.walk(base):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(d, f)
                m = os.path.relpath(p, SRC)[:-5].replace('/', '.')
                mods[m] = [l.split()[1][len(CPKG) + 1:] for l in open(p) if l.startswith('import ' + CPKG + '.')]
    return mods


def forked_modules(mods):
    rev = collections.defaultdict(set)
    for m, ds in mods.items():
        for d in ds:
            rev[d].add(m)
    seen, todo = {ROOT_MOD}, [ROOT_MOD]
    while todo:
        x = todo.pop()
        for y in rev[x]:
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return {m for m in seen if m not in EXCLUDE and '.IntermediateCount.' not in m}


def declarations(text):
    """(namespace, full name) of every declaration, tracking `namespace`/`end`."""
    out, stack = [], []
    for line in text.split('\n'):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r'^end\s+(\S+)', line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(1)
            if name.startswith('_root_.'):
                out.append(('', name[7:]))
            else:
                ns = '.'.join(stack)
                out.append((ns, (ns + '.' + name) if ns else name))
    return out


def new_module(m):
    return f'{PKG}.ReturnD.' + m[len('Record1252270103Return.'):]


def main():
    out, sp = sys.argv[1], sys.argv[2]
    patches = FP.patches(sp)
    mods = all_modules()
    fork = sorted(forked_modules(mods))
    texts = {m: open(os.path.join(SRC, m.replace('.', '/') + '.lean')).read() for m in fork}
    fork_names, ns_forked, ns_unforked = set(), set(), set()
    for m, ds in mods.items():
        text = texts.get(m) or open(os.path.join(SRC, m.replace('.', '/') + '.lean')).read()
        for ns, full in declarations(text):
            if m in texts:
                fork_names.add(full)
                ns_forked.add(ns)
            else:
                ns_unforked.add(ns)
    fork_names = {n for n in fork_names if n.startswith(NS_OLD + '.')}
    only_forked = {ns for ns in ns_forked if ns not in ns_unforked and ns.startswith(NS_OLD + '.')}
    qual = re.compile(r"(?<![A-Za-z_0-9.'])" + re.escape(NS_OLD) + r"((?:\.[A-Za-z_][A-Za-z_0-9'!?]*)+)")

    def requal(mt):
        full = NS_OLD + mt.group(1)
        # longest forked prefix of the dotted name (a declaration, possibly followed by a field)
        parts = mt.group(1).split('.')[1:]
        for k in range(len(parts), 0, -1):
            cand = NS_OLD + '.' + '.'.join(parts[:k])
            if cand in fork_names or cand in only_forked:
                return NS_NEW + '.' + '.'.join(parts)
        return full

    for m in fork:
        t = texts[m]
        lines = []
        stack = []          # Collet's namespaces, as in the original file
        for line in t.split('\n'):
            mns = re.match(r'^namespace\s+(\S+)', line)
            if mns:
                stack.append(mns.group(1))
            mne = re.match(r'^end\s+(\S+)', line)
            if mne and stack and stack[-1] == mne.group(1):
                stack.pop()
            mi = re.match(r'^import\s+(\S+)', line)
            if mi:
                tgt = mi.group(1)
                if tgt.startswith(CPKG + '.') and tgt[len(CPKG) + 1:] in texts:
                    line = 'import ' + new_module(tgt[len(CPKG) + 1:])
                lines.append(line)
                continue
            if line.startswith('#print axioms'):
                continue
            mn = re.match(r'^namespace\s+' + re.escape(NS_OLD) + r'(\S*)$', line)
            if mn:
                lines.append(f'namespace {NS_NEW}{mn.group(1)}')
                # Collet's ancestors of the old namespace, for the unforked names they resolved
                parts = [p for p in mn.group(1).split('.') if p]
                prefixes = [NS_OLD] + [NS_OLD + '.' + '.'.join(parts[:k]) for k in range(1, len(parts))]
                # a namespace holding only forked declarations need not (and may not) exist in Collet's
                prefixes = [p for p in prefixes if p not in only_forked]
                lines.append('open ' + ' '.join(prefixes))
                continue
            me = re.match(r'^end\s+' + re.escape(NS_OLD) + r'(\S*)$', line)
            if me:
                lines.append(f'end {NS_NEW}{me.group(1)}')
                continue
            mo = re.match(r'^(\s*open\s+(?:scoped\s+)?)(.*)$', line)
            if mo and not line.lstrip().startswith('open scoped'):
                toks = []
                cur = '.'.join(stack)
                scopes = [cur[:i] for i in range(len(cur), 0, -1) if i == len(cur) or cur[i] == '.']
                for tok in mo.group(2).split():
                    if tok in only_forked:
                        toks.append(NS_NEW + tok[len(NS_OLD):])
                        continue
                    # a namespace named relative to the current namespace or to Collet's root
                    hit = next((sc + '.' + tok for sc in scopes + [NS_OLD] if sc + '.' + tok in only_forked), None)
                    toks.append(NS_NEW + hit[len(NS_OLD):] if hit else tok)
                line = mo.group(1) + ' '.join(toks)
            lines.append(qual.sub(requal, line))
        body = '\n'.join(lines)
        rel = m[len('Record1252270103Return.'):]
        path = os.path.join(out, 'ReturnD', rel.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(path), exist_ok=True)
        if rel in FP.HAND:
            write_if_changed(path, open(os.path.join(HERE, FP.HAND[rel])).read())
            continue
        for old, new in FP.GLOBAL:
            body = body.replace(old, new)
        for old, new in patches.get(rel, []):
            if body.count(old) != 1:
                raise SystemExit(f'patch for {rel} applies {body.count(old)} times:\n{old}')
            body = body.replace(old, new)
        write_if_changed(path, HDR.format(m=rel) + body)
    print(f'forked {len(fork)} modules, {len(fork_names)} declarations, '
          f'{len(only_forked)} namespaces re-pointed')


if __name__ == '__main__':
    main()
