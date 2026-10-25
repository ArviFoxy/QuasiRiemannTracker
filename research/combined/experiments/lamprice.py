# Price of the start face's slope: P-face intercept from the flow started at the tangency, and the
# return's sensitivity to the P intercept.
import sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/faceless-chain')
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
import closed_flow as CF, theta_eval as T
from scipy.optimize import brentq
den, phi = 2**-15, 1e-4
def pface(B0, lam):
    s0 = brentq(lambda s: CF.slope(s, B0 - lam*s, den, phi) - lam, 1e-4, 0.059, xtol=1e-14)
    ss, Es = CF.flow(s0, B0 - lam*s0, 0.06, 60000, den=den, fudge=phi)
    sl = [CF.slope(s, E, den, phi) for s, E in zip(ss, Es)]
    i = next(k for k in range(len(sl)) if sl[k] <= 3)
    return s0, ss[i], Es[i] + 3*ss[i]
for lam in (3.72, 3.65, 3.6, 3.5, 3.4):
    s0, sP, BP = pface(0.99999, lam)
    print(f"lam={lam}: tangency s0={s0:.6f}, slope-3 point s={sP:.5f}, P intercept={BP:.6f}", flush=True)
f = json.load(open(sys.argv[1]))
C = (Fr(f[0]['B']), Fr(f[0]['L']), Fr(f[0]['cap'])); P = (Fr(f[1]['B']), Fr(f[1]['L']), Fr(f[1]['cap']))
for dB in (Fr(0), Fr(1, 10**4), Fr(2, 10**4)):
    print("dB_P", float(dB), "theta*", T.theta_star(C, (P[0] + dB, P[1], P[2]), lo=8744000, hi=8746300), flush=True)
