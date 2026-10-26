"""Type-split twins (mixed step, L4/L5).

A Collet lemma whose `s : Input α` plays only the first-layer role (columns, labels, keys,
dictionary rays, `s.η`) but shares its slot type `α` with second-layer objects (`T F : Finset α`,
`w : α → ℝ`, `datum : _ → SecondInputDatum α`, `InitialAffineAt (α:=α)`) is restated with the first
layer over its own type: `(s : Input α)(modifier : Tuple α→ℂ)` becomes
`{α₀ : Type}[Fintype α₀][DecidableEq α₀](s : Input α₀)(modifier : Tuple α₀→ℂ)`.
The proof text is Collet's: `intro … second s modifier …` gets the three new binders, and calls of
other split lemmas are re-pointed to their `_mx` twins.

usage: python3 typesplit.py SRC_REL OUT_REL 'name1,name2' 'renamed1,renamed2' [extra imports...]
  SRC_REL: path of Collet's module relative to Record1252270103Source (e.g. Admission/RetainedLowPaid)
  names: the theorems to restate (in this module); renamed: theorems of other modules already split
"""
import re, sys, os
CROOT = '/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/Record1252270103Source'
OROOT = '/home/user/lean-env/qrh/Submissions/arvi_mixed_step/ForkMx/Record1252270103Source'
CPKG = 'Submissions.hailey_collet_1252270103.Record1252270103Source'
MPKG = 'Submissions.arvi_mixed_step.ForkMx.Record1252270103Source'

def main():
    src_rel, out_rel, names, renamed = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    extra = sys.argv[5:]
    names = [n for n in names.split(',') if n]
    renamed = [n for n in renamed.split(',') if n]
    text = open(os.path.join(CROOT, src_rel + '.lean')).read()
    lines = text.split('\n')
    first = lines[0]
    # header block: everything up to the first declaration we fork
    starts = {}
    for n in names:
        m = re.search(r'^(theorem|lemma) ' + re.escape(n) + r'\b', text, re.M)
        assert m, n
        starts[n] = m.start()
    cut = min(starts.values())
    head = text[:cut]
    # drop the imports from the head (we import the original module instead) and the copyright block
    head_lines = head.split('\n')
    i = 0
    while i < len(head_lines) and not head_lines[i].startswith('set_option'):
        i += 1
    head_body = '\n'.join(head_lines[i:])
    # make anonymous local instances / named local instances unique
    head_body = re.sub(r'^(local instance)\s+([A-Za-z_][A-Za-z_0-9]*)', r'\1 \2_mx', head_body, flags=re.M)
    head_body = re.sub(r'^(local instance)\s*(\{)', r'\1 typesplitInst_mx \2', head_body, flags=re.M)
    # declarations other than the forked ones in head are dropped (they exist in the original)
    out_decls = []
    for n in names:
        s0 = starts[n]
        m = re.search(r'^(theorem|lemma|def|end\b|#print|section|namespace|private)', text[s0 + 5:], re.M)
        e0 = s0 + 5 + m.start() if m else len(text)
        d = text[s0:e0].rstrip() + '\n'
        d = re.sub(r'^(theorem|lemma) ' + re.escape(n) + r'\b', r'\1 ' + n + '_mx', d, count=1, flags=re.M)
        before = d
        d = re.sub(r'\(s\s*:\s*Input α\)\s*\(modifier\s*:\s*CenteredMomentAddedZeroUniform\.Tuple α→ℂ\)',
                   '{α₀ : Type}[Fintype α₀][DecidableEq α₀](s : Input α₀)(modifier : CenteredMomentAddedZeroUniform.Tuple α₀→ℂ)', d)
        assert d != before, 'no s binder in ' + n
        # intro patterns
        d = re.sub(r'(\bintro\b[^:]*?\bsecond)\s+s\s+modifier\b', r'\1 α₀ _ _ s modifier', d, flags=re.S)
        for r in renamed + names:
            d = re.sub(r'(?<![A-Za-z_0-9.])((?:[A-Za-z_][A-Za-z_0-9]*\.)*)' + re.escape(r) + r'(?![A-Za-z_0-9_\'])', r'\1' + r + '_mx', d)
        # the theorem's own name was already renamed; undo double suffix
        d = d.replace(n + '_mx_mx', n + '_mx')
        out_decls.append(d)
    ns = re.findall(r'^namespace (\S+)', head, re.M)
    ends = '\n'.join(['end'] * head_body.count('noncomputable section')) + ''
    tail = ''
    if 'noncomputable section' in head_body:
        tail += 'end\n'
    for n in reversed(ns):
        tail += 'end ' + n + '\n'
    hdr = (first + '\n' +
           f'Mixed step (L4/L5, F3): fork of Record1252270103Source.{src_rel.replace("/", ".")}; changes: type split\n'
           '(the first layer `s : Input α₀` is typed apart from the second-layer slots `α`; proofs verbatim). -/\n')
    imports = [f'import {CPKG}.{src_rel.replace("/", ".")}'] + [f'import {x}' for x in extra]
    out = hdr + '\n'.join(imports) + '\n' + head_body + '\n'.join(out_decls) + '\n' + tail
    for n in names:
        nsfull = ns[-1] if ns else ''
        out += f'#print axioms {nsfull}.{n}_mx\n'
    path = os.path.join(OROOT, out_rel + '.lean')
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w').write(out)
    print('wrote', path)

main()
