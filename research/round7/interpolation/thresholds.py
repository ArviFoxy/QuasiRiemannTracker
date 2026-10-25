"""Precise thresholds at the binding corner (PR69 face C, delta=0.4546, p=1/2) + resonance-model checks."""
import numpy as np
from corner_check import corner
from resonance_model import build
delta = 0.4546
R, t, r, m = corner(delta, 0.5, 0.96226151753982, 3.14813176381578)
target = R - 7.5e-5
nu_beurling = m/(2*np.pi)                         # dip needs zero density >= m*/(2pi) * log U per unit height
nu_littlewood = (1 - target)/(4*np.pi*delta)      # Littlewood + unmarked 4th moment counts density >= this
print(f"corner: R={R:.6f} r*={r:.5f} m*={m:.5f} t*={t:.5f}")
print(f"Beurling/Ingham dip threshold density nu_B = m*/(2pi) = {nu_beurling:.6f}  (spacing 2pi/(m* logU) = {2*np.pi/m:.3f}/logU)")
print(f"Littlewood+4th-moment needs nu >= {nu_littlewood:.6f}  (ratio {nu_littlewood/nu_beurling:.4f})")
print(f"Littlewood count at nu_B: 1 - 2*delta*m* = {1-2*delta*m:.5f}   vs R = {R:.5f};  slot term of P line = {1-2*delta*m-R:.5f}")
print(f"Margins of the 'every m<=1/2 has a multiple in (r*,t*)' argument: 2m*-r* = {2*m-r:.4f}, t*-1 = {t-1:.4f}")
# resonance model: log|P(Y)| along vertical lines (Y = e^{-m1 L (x-a)} e^{-i m1 L t}) -> average over t
d, k2 = 5, 14; m1 = m/d
zeta, S, P, A = build(d, k2)
th = np.linspace(0, 2*np.pi, 20001)[:-1]
for X in [-0.05, -0.01, 0.0, 0.01, 0.05, 0.1, 0.2]:      # X = a - x  (X>0: left of the zero line)
    for Lval in [1000.0]:
        rad = np.exp(m1*Lval*X)                      # |Y|
        vals = np.log(np.abs(P(rad*np.exp(1j*th))))/Lval
        print(f"  x = a{-X:+.2f}: mean log_U|L| = {vals.mean():+.5f}  (line-charge prediction {max(0,m*X):.5f}),  min = {vals.min():+.4f}, max = {vals.max():+.4f}")
