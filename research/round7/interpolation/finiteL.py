import numpy as np, sys
from poly_dip import nmin as poly_nmin
from scan_trig import kmin
for L in [100, 200, 400]:
    n = poly_nmin(L, 1.0, bounded=False)
    out = [f"L={L}: tight-cluster(poly, unbounded) terms={n+1} kappa={(n+1)/L:.4f}"]
    for om in [2.0, 6.0]:
        k = kmin(L, om, bounded=False)
        out.append(f"trig(om={om}) k={k} kappa={k/L:.4f}")
    print(" | ".join(out), flush=True)
