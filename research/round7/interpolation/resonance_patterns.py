"""Resonance model: compare occupied patterns S (contiguous vs Beatty/Sturmian) for coefficient sizes."""
import numpy as np
from resonance_model import build, taylor_inverse
for (d, k2) in [(5, 14), (9, 25), (14, 39), (24, 67), (43, 120)]:
    k1 = k2 - d
    for name, S in [("contiguous", list(range(d))), ("beatty", sorted({int(np.floor(j*k2/d)) for j in range(d)}))]:
        if len(S) != d: continue
        zeta, S_, P, A = build(d, k2, S=S)
        a = taylor_inverse(P, 4*k2)
        gap = np.abs(a[k1+1:k2]).max()
        print(f"d={d:2d} k2={k2:3d} (r/m={k1/d:.4f}) {name:10s}: max|P coeff|={np.abs(P.coeffs).max():9.3g}  "
              f"max|1/P coeff| (k<4k2)={np.abs(a).max():9.3g}  |a_k1|={abs(a[k1]):.3f} |a_k2|={abs(a[k2]):.3f}  max gap coeff={gap:.1e}")
