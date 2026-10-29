"""Step 6: sensitivities at the binding point: d(maxE)/dh, d(maxE)/dtheta, and the floor-margin constraint."""
import mpmath as mp
from fractions import Fraction as Fr
from theta_star import maxE
from model import hceiling

mp.mp.dps = 40
th = Fr(43693617, 50000000)
h0 = Fr(8044451, 10000000)
e0, d0, _ = maxE(th, h0)
eps = Fr(1, 10 ** 9)
eh, _, _ = maxE(th, h0 + eps)
et, _, _ = maxE(th + eps, h0)
dEdh = (eh - e0) / mp.mpf(1e-9)
dEdt = (et - e0) / mp.mpf(1e-9)
print('max E =', mp.nstr(e0, 15), ' delta* =', mp.nstr(d0, 10))
print('dE/dh (theta fixed) =', mp.nstr(dEdh, 6), '   dE/dtheta (h fixed) =', mp.nstr(dEdt, 6))
# floor ceiling h <= a*theta + b
hc1, hc2 = hceiling(th), hceiling(th + Fr(1, 10 ** 6))
slope = (hc2 - hc1) / Fr(1, 10 ** 6)
print('floor ceiling slope dh/dtheta =', float(slope), ' => total dE/dtheta along the ceiling =', mp.nstr(dEdt + dEdh * mp.mpf(float(slope)), 6))
# the exponent at the binding point as a function of h (theta fixed): decreasing, so h sits at the ceiling
for hh in ['0.8030', '0.8040', '0.8044451', '0.8050', '0.8060']:
    print(f'  h={hh}  maxE={mp.nstr(maxE(th, Fr(hh))[0], 12)}')
