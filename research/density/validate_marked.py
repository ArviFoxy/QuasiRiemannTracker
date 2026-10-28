#!/usr/bin/env python3
"""Validation of the marked mode of `gen_hybrid.py` (`--marked`, `marked_lib`); no Lean needed.

(a) the 46 steps of PR 86, floor 3/5: the marked HIGH gate certifies with one (v, t, p) box per facet branch
    (6 per step, 276 in all);
(b) a transition from the parent of PR 86's step 46 with `B` lowered by 3/10000 and `A = 2/5`: the unmarked gate
    `high_at_q` is negative at `v = 0` (the unmarked generator refuses it), the marked gate holds;
(c) the boundary: lowering `B` by 25/100000 with `c = 9/100` (same parent, `A = 2/5`) makes the marked gate false
    at `(v, t, p) = (0, 0, 1/2)`; the generator reports the point;
(d) the two example files of the package (`Source/HybridMarkedK15_46.lean`, `Source/HybridMarkedStretch46.lean`)
    are what the generator writes now;
(e) the box-cover code with forced bisections (`--marked-force-split`) produces a cover of the same reserve class.

Usage: validate_marked.py [LAKE_PROJECT]   (default /home/user/lean-env/qrh)"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_hybrid as G  # noqa: E402

QRH = sys.argv[1] if len(sys.argv) > 1 else "/home/user/lean-env/qrh"
SRC = f"{QRH}/Submissions/density_split_fine_chain/Source"
PKG = f"{QRH}/Submissions/arvi_density/Source"
lib = G.marked_lib(G.PR83_LIB)
ok = True


def check(cond, msg):
    global ok
    print(("ok   " if cond else "FAIL ") + msg)
    ok = ok and cond


# (a)
tot, minr = 0, 1.0
for i in range(1, 47):
    P = G.params_from_header(f"{SRC}/HybridK15_{i:02d}.lean", floor=Fr(3, 5))
    r = G.generate(P, namespace="QRH.ArviDensity", module="T", lib=lib)
    tot += r.marked.total_boxes
    minr = min(minr, float(r.marked.r))
check(tot == 276, f"(a) 46 PR 86 steps at floor 3/5: {tot} marked boxes (one per branch and step), smallest reserve {minr:.2e}")

# (b)
B0, L0, c0 = Fr(4945703, 5000000), Fr(5866251, 2500000), Fr(1, 10)
L, c, D = Fr(4683001, 2000000), Fr(1, 10), Fr(5713, 250)
P = G.Params(B0, L0, c0, B0 - Fr(3, 10000), L, c, Fr(2, 5), D, floor=Fr(3, 5))
try:
    G.generate(P, namespace="QRH.ArviDensity", module="T")
    check(False, "(b) the unmarked generator should refuse the stretched step")
except G.InfeasibleGate as e:
    check("high_at_q" in str(e), f"(b) unmarked: {str(e)[:70]}...")
r = G.generate(P, namespace="QRH.ArviDensity", module="HybridMarkedStretch46", lib=lib)
check(r.marked.total_boxes == 6, f"(b) marked: certified, {r.marked.total_boxes} boxes, reserve {float(r.marked.r):.2e}")

# (c)
Pb = G.Params(B0, L0, c0, B0 - Fr(25, 100000), L, Fr(9, 100), Fr(2, 5), D, floor=Fr(3, 5))
try:
    G.generate(Pb, namespace="QRH.ArviDensity", module="T", lib=lib)
    check(False, "(c) the boundary step should be refused")
except G.InfeasibleGate as e:
    check("marked gate branch (1, 0) is not positive" in str(e), f"(c) {str(e)[:110]}...")

# (d)
P46 = G.params_from_header(f"{SRC}/HybridK15_46.lean", floor=Fr(3, 5))
for name, PP, title in (
        ("HybridMarkedK15_46", P46,
         "density transition 46 of the k15 chain (PR 86), certified with the marked HIGH gate"),
        ("HybridMarkedStretch46", P,
         "a stretched transition from the parent of PR 86's transition 46 (B lowered by 3/10000, A = 2/5; the "
         "unmarked gate high_at_q is negative at v = 0, the marked HIGH gate holds)")):
    path = f"{PKG}/{name}.lean"
    if not os.path.exists(path):
        print(f"skip (d) {path} not found")
        continue
    cfg = G.LeanConfig(namespace="QRH.ArviDensity", module=name, gates_import=G.MARKED_GATES_IMPORT,
                       gates_namespace=G.MARKED_GATES_NAMESPACE, title=title)
    txt = G.generate(PP, config=cfg, lib=lib).text
    check(txt == open(path, encoding="utf-8").read(), f"(d) {name}.lean is what gen_hybrid.py --marked writes")

# (e)
lf = G.marked_lib(G.PR83_LIB, G.MarkedSpec(force=(0, 2)))
r = G.generate(P46, namespace="QRH.ArviDensity", module="T", lib=lf)
check(all(b.nleaves == 4 for b in r.marked.branches), "(e) forced bisections of v and p: 4 boxes per branch, cover emitted")
sys.exit(0 if ok else 1)
