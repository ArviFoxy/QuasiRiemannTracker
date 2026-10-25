import sys
from fractions import Fraction as Fr
import family2 as F2, polyq as P, theta_eval as T
sig = [float(x) for x in sys.argv[1].split(',')]
fam, _ = F2.build2(sig, m=16)
(jC, iC), (jP, iP) = F2.face_C(fam), F2.face_P(fam)
B, L, B0, L0, sv = fam.polys(jC)
yC = iC*fam.Dy
BC, LC = P.ev(B, yC), P.ev(L, yC)
assert P.ev(B0, yC) > Fr(22, 23)
B, L, B0, L0, svP = fam.polys(jP)
yP = iP*fam.Dy
BP, LP = P.ev(B, yP), P.ev(L, yP)
print("C: y=1-Dy s=%.9f B=%.10f L=%.8f | P: piece %d i=%d s=%.9f B=%.10f L=%.8f" % (float(P.ev(sv, yC)), float(BC), float(LC), jP, iP, float(P.ev(svP, yP)), float(BP), float(LP)), flush=True)
th = T.theta_star((BC, LC, F2.CAPMAX), (BP, LP, F2.CAPMAX))
print("theta* =", th, " (iP =", iP, ")")
