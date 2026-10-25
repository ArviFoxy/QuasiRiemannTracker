import sys, numpy as np
from fractions import Fraction as Fr
import family as Fm, theta_eval as T
sig = [float(x) for x in sys.argv[1].split(',')]; den = float(sys.argv[2]); phi = float(sys.argv[3])
fam, _ = Fm.build(sig, den, phi)
D = fam.Delta
# last grid point with HIGH parent B >= 22/23
send = Fm.rat(sig[-1], 10**7)
k = int((send - fam.sig[0])/D)
sC = fam.sig[0] + k*D
while fam.node(sC - D)[0] < Fr(22, 23): sC -= D
BC, LC = fam.node(sC)
# P: largest s with L > 3
lo, hi = fam.sig[0], sC
for _ in range(60):
    mid = fam.sig[0] + ((lo + hi)/2 - fam.sig[0])//D*D
    if fam.node(mid)[1] > 3: lo = mid
    else: hi = mid
    if hi - lo <= D: break
sP = lo
BP, LP = fam.node(sP)
print(f"C: s={float(sC):.7f} B={float(BC):.9f} L={float(LC):.7f}   P: s={float(sP):.7f} B={float(BP):.9f} L={float(LP):.7f}", flush=True)
C = (BC, LC, Fm.CAPMAX); P = (BP, LP, Fm.CAPMAX)
C = tuple(Fr(x).limit_denominator(10**13) if i < 2 else x for i, x in enumerate(C))
P = tuple(Fr(x).limit_denominator(10**13) if i < 2 else x for i, x in enumerate(P))
print("theta* =", T.theta_star(C, P))
