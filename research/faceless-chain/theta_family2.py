import sys
from fractions import Fraction as Fr
import family2 as F2, polyq as P, theta_eval as T
sig = [float(x) for x in sys.argv[1].split(',')]
fam, _ = F2.build2(sig, m=16)
j = len(fam.H) - 1
B, L, B0, L0, sv = fam.polys(j)
yC = 1 - fam.Dy
BC, LC = P.ev(B, yC), P.ev(L, yC)
assert P.ev(B0, yC) > Fr(22, 23)
# P face: largest grid y in the last piece with L > 3
lo, hi = 0, 2**16 - 1
while hi - lo > 1:
    mid = (lo + hi)//2
    if P.ev(L, Fr(mid, 2**16)) > 3: lo = mid
    else: hi = mid
yP = Fr(lo, 2**16)
BP, LP = P.ev(B, yP), P.ev(L, yP)
print("C: y=1-Dy s=%.9f B=%.10f L=%.8f | P: i=%d s=%.9f B=%.10f L=%.8f" % (float(P.ev(sv, yC)), float(BC), float(LC), lo, float(P.ev(sv, yP)), float(BP), float(LP)), flush=True)
th = T.theta_star((BC, LC, F2.CAPMAX), (BP, LP, F2.CAPMAX))
print("theta* =", th, " (iP =", lo, ")")
