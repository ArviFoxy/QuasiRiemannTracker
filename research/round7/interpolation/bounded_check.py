import numpy as np
from expsum_dip import solve, trig_config
L = 200.0
for om in [12.0, 14.0]:
    for k in [16, 22, 28, 36, 48]:
        t, y = solve(trig_config(k, om, L), L, bounded=True, nout=500)
        rot = np.angle(y[1:]/y[:-1]) if y is not None else None
        med = np.median(np.mod(rot, 2*np.pi)) if rot is not None else np.nan
        print(f"L={L:.0f} omega={om} k={k} kappa={k/L:.3f}  t_bounded={t:.3e}  median phase step={med:.3f} rad"
              f"  (omega*r1 mod 2pi = {np.mod(-om*0.7413, 2*np.pi):.3f})", flush=True)
