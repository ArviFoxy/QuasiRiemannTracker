"""theta* (relaxed return guards, pointwise full-face count = max of both pieces) vs the end of the E5 line."""
import numpy as np
from ideal import face_count, theta_star
d = np.round(np.arange(0.30, 0.62, 0.0005), 6)
p = np.round(np.concatenate([np.arange(0.30, 0.49, 0.01), [0.49, 0.495, 0.499, 0.5]]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')
capf = lambda L: 0.1 + 0.06 * (5143 / 2000 - L)
base = None
for Lc in (2.10, 2.05, 2.02, 2.01, 2.005, 2.003, 2.0):
    for Lp in sorted({Lc, 2.02}):
        ok, v = face_count(DD, PP, 0.99999, Lc, capf(Lc))
        env = np.where(ok, v, np.inf)
        th, k, oc = theta_star(DD, PP, env, pL=Lp)
        if base is None: base = th
        print('count face L=%.3f cap=%.4f, physical L=%.3f: theta* = %.8f  (d=%.4f p=%.3f)' % (Lc, capf(Lc), Lp, th, d[k[0]], p[k[1]]))
