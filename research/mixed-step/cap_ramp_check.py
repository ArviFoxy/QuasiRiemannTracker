"""Feasibility of a growing face cap on the last family piece (count-face cap lever, Lemma W report §3):
cap(y) = cap0 + kappa*y on piece J; exact SourceValid3 checks (mixed_certs.check_node) at sample faces,
with the node's cap cap(y) and the parent's cap(y - Dy).
usage: QRH_K=9/2 python3 cap_ramp_check.py PIECE CAP_END [nsample]"""
import sys, random
from fractions import Fraction as Fr
import gen_family3 as G
import polyq as P
import mixed_certs as MC

fam, fan = G.build()
j = int(sys.argv[1]); cap_end = Fr(sys.argv[2]); ns = int(sys.argv[3]) if len(sys.argv) > 3 else 12
cap0 = G.CAP
kappa = cap_end - cap0
cap = lambda y: cap0 + kappa*y
B, L, B0, L0 = fam.polys(j)
random.seed(1)
ys = [fam.Dy, Fr(1, 4), Fr(1, 2), Fr(3, 4), 1 - fam.Dy] + [Fr(random.randrange(1, 2**16 - 1), 2**16) for _ in range(ns)]
bad = 0
for y in ys:
    b, l, b0, l0 = P.ev(B, y), P.ev(L, y), P.ev(B0, y), P.ev(L0, y)
    q = (1 - G.DEN)*l0/(6*b0 - l0)
    n = MC.face(b, l, cap(y), q)
    low = MC.face(b0, l0, cap(y - fam.Dy))
    ok, msgs, _ = MC.check_node(n, low, low, Fr(8))
    cell = MC.cell_ok(n, low)
    w = MC.weakCap(n, low, n['cap'])
    if not (ok and cell):
        bad += 1
    print(f"y={float(y):.5f} cap={float(cap(y)):.5f} ok={ok and cell} weak@cap={float(w):.3e} {msgs[:2] if not ok else ''}", flush=True)
print("ALL OK" if bad == 0 else f"{bad} failures")
