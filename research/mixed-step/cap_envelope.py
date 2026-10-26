"""Max feasible cap along a family piece (exact SourceValid3 + cell checks, mixed_certs.check_node):
for each sample y, bisect the node's cap b_max(y) with the parent cap fixed at c_par (the step's cap
can jump from the parent's cap). Tells how high the count/physical faces' caps can go.
usage: QRH_K=9/2 python3 cap_envelope.py PIECE C_PARENT [ys...]
C_PARENT = "ramp:EPS" sets the parent cap to cap - EPS (a continuous ramp)."""
import sys
from fractions import Fraction as Fr
import gen_family3 as G
import polyq as P
import mixed_certs as MC

fam, fan = G.build()
j = int(sys.argv[1])
RAMP = sys.argv[2].startswith('ramp:')
cpar = Fr(sys.argv[2][5:]) if RAMP else Fr(sys.argv[2])
ys = [Fr(y) for y in sys.argv[3:]] or [fam.Dy, Fr(1, 4), Fr(35747, 65536), Fr(3, 4), 1 - fam.Dy]
B, L, B0, L0 = fam.polys(j)


def ok(y, cap):
    b, l, b0, l0 = P.ev(B, y), P.ev(L, y), P.ev(B0, y), P.ev(L0, y)
    q = (1 - G.DEN)*l0/(6*b0 - l0)
    n = MC.face(b, l, cap, q)
    low = MC.face(b0, l0, cap - cpar if RAMP else cpar)
    good, msgs, _ = MC.check_node(n, low, low, Fr(8))
    return good and MC.cell_ok(n, low), msgs


for y in ys:
    lo, hi = Fr(3, 40), Fr(15, 100)
    assert ok(y, lo)[0], (float(y), ok(y, lo)[1][:2])
    for _ in range(18):
        mid = (lo + hi)/2
        if ok(y, mid)[0]:
            lo = mid
        else:
            hi = mid
    print(f"y={float(y):.5f}  b_max={float(lo):.6f}  first failure above: {ok(y, hi)[1][:1]}", flush=True)
