import numpy as np
from circle_lp import solve
from common import R1, R2
wmax = 2*np.pi/(R2-R1)
print("omega_max (arc = full circle) =", wmax)
for omega in [12.0, 12.566, 13.0, 13.5, 14.0, 14.43, 14.7, 15.0, 15.1, 15.15]:
    kb, Z, w = solve(omega, bounded=True)
    dens = 1/omega   # zeros per unit height, in units of L
    phi_lw = 2*np.pi*dens*(0.4546/2)   # Littlewood mean of log_U|L(1/2+it)| for zeros at Re=a
    print(f"omega={omega:7.3f} kappa_bounded={kb:.5f} span={kb*omega:.3f}  density={dens:.4f}  "
          f"Littlewood mean log_U|L(1/2)|={phi_lw:.4f}  4th-moment count={1-4*phi_lw:.4f}", flush=True)
