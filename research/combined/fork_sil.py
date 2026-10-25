"""Vendor Sil's fourth-power source face (upstream PR 74, `sil-fourth-power-20261025`, Apache-2.0)
into our package, with the contrary hypothesis weakened.

Sil proves `GlobalSource (99999/100000) (93/25) (3/50)`
(`RepairedRestrictedSource.actual_global_source`) under `theta < beta`, with the PR 74
`theta = 1749387/2000000`. The construction uses that hypothesis only through
`contrary_inputs hcontra).1 : 51/100 ≤ beta`. This script copies the import closure of that
theorem and replaces the hypothesis by `51/100 ≤ beta` in the eight files that state or pass it.
Nothing else changes: the import paths move into our package, and the namespaces and proofs stay as
they are.

usage: python3 fork_sil.py SIL_SRC OUT_DIR PKG
  SIL_SRC  the directory `submissions/sil-fourth-power-20261025/src/Candidate/FourthPower` of PR 74
  OUT_DIR  the target directory, e.g. `.../Submissions/arvi_repeated_marks_on_sil_face_20261025/FourthPower`
  PKG      the module prefix of OUT_DIR, e.g. `Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower`
"""
import os, re, sys

ROOT = 'RepairedRestrictedSource'          # the module of `actual_global_source`
OLD = 'Candidate.FourthPower'
NOTE = ("Modified by Arvi (2026-10-25): the contrary hypothesis `theta < beta` is replaced by\n"
        "`51/100 ≤ beta`, the only consequence of it that the source construction uses.\n")
HYP_OLD = 'theta < HeckeZeroSupremum.beta'
HYP_NEW = '(51/100:ℝ) ≤ HeckeZeroSupremum.beta'

# (file, old, new, expected number of occurrences)
EDITS = [
    ('RepairedSourceSideSupply', f'def ContraryRawSideProvider : Prop :=\n  {HYP_OLD} →',
     f'def ContraryRawSideProvider : Prop :=\n  {HYP_NEW} →', 1),
    ('RepairedContributionContract', f'def PendingSmallContribution : Prop :=\n  {HYP_OLD} →',
     f'def PendingSmallContribution : Prop :=\n  {HYP_NEW} →', 1),
    ('RepairedActualSideProvider', 'have hβ := (RepairedRootParameters.contrary_inputs hcontra).1',
     'have hβ := hcontra', 1),
    ('RepairedCombinedSideFromSmall', 'have hβ := (contrary_inputs hcontra).1', 'have hβ := hcontra', 1),
    ('RepairedSourceBallSupply', f'(hcontra : {HYP_OLD})', f'(hcontra : {HYP_NEW})', 1),
    ('RepairedSourceActualBall', f'(hcontra : {HYP_OLD})', f'(hcontra : {HYP_NEW})', 1),
    ('RepairedSourceSetupBound', f'(hcontra : {HYP_OLD})', f'(hcontra : {HYP_NEW})', 1),
    ('RepairedRestrictedSource', f'(hcontra : {HYP_OLD})', f'(hcontra : {HYP_NEW})', 5),
    ('RepairedRestrictedSource', 'Constructs the restricted unit source in the contrary branch theta < beta',
     'Constructs the restricted unit source for every beta ≥ 51/100', 1),
]


# modules that keep their (still true, now unused) statements under the hypothesis
KEEP = {'IncumbentInput', 'RepairedRootParameters'}


def imports(src, mod):
    return re.findall(rf'^import\s+{re.escape(OLD)}\.(\S+)', open(os.path.join(src, mod + '.lean')).read(), re.M)


def closure(src, root):
    seen, stack = set(), [root]
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack += imports(src, m)
    return sorted(seen)


def main(src, out, pkg):
    mods = closure(src, ROOT)
    texts = {m: open(os.path.join(src, m + '.lean')).read() for m in mods}
    for m, old, new, count in EDITS:
        n = texts[m].count(old)
        assert n == count, (m, old, n)
        texts[m] = texts[m].replace(old, new)
    edited = sorted({m for m, *_ in EDITS})
    for m in edited:
        t = texts[m]
        assert HYP_OLD not in t and 'contrary_inputs' not in t, m
        head, rest = t.split('\n', 1)           # the copyright line opens the header comment
        assert head.startswith('/- Copyright'), m
        texts[m] = head + '\n' + NOTE + rest
    # Only `contrary_inputs` (and Sil's case split `target_cases`) still state the hypothesis, and
    # no module of the closure uses them any more.
    for m in mods:
        assert m in edited or m in KEEP or HYP_OLD not in texts[m], m
        assert m in KEEP or 'contrary_inputs' not in texts[m], m
    os.makedirs(out, exist_ok=True)
    for m in mods:
        t = re.sub(rf'^import\s+{re.escape(OLD)}\.', f'import {pkg}.', texts[m], flags=re.M)
        open(os.path.join(out, m + '.lean'), 'w').write(t)
    lines = sum(texts[m].count('\n') for m in mods)
    print(f"{len(mods)} modules ({lines} lines) copied, {len(edited)} edited: {', '.join(edited)}")


if __name__ == '__main__':
    main(*sys.argv[1:4])
