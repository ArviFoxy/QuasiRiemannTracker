import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
import numpy as np, worth, fast, ideal
from ideal import face_count
B, L, h = 0.99999, 2.0001, 0.8097
cap = 0.1 + 0.06*(5143/2000 - L)
fast.branch = worth.make_branch(5/6); ideal.branch = fast.branch
th = 0.873382278649624; c = 1-th; kappa = 1-2*c
ell = 4*c - 1/3; y = h - 2*ell; dd = h + 1e-10
C = min(0.075*dd, (2*y - (2-B)*dd)/L)
d = np.round(np.arange(0.02, 0.751, 0.002), 6)
p = np.round(np.arange(0.0, 0.5001, 0.01), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')
ok, v = face_count(DD, PP, B, L, cap)
env = np.where(ok, v, np.inf)
oc = worth.old_count(DD, PP, kappa, 5/6)
e = np.minimum(env, oc)
E = 0.5 + 13*h/75 - y/2 - ell/2 - 0.09*dd + DD/2 + DD*PP*(ell - C/2) + 0.75*dd*e
gap = E - th
k = np.unravel_index(np.argmax(gap), gap.shape)
print('global max gap %.3e at delta %.3f p %.2f' % (gap[k], DD[k], PP[k]))
# top-10 local regions: show max gap per p
for j in range(0, len(p), 5):
    kk = np.argmax(gap[:, j]); print('p %.2f: max gap %+.3e at delta %.3f (count %.4f, face ok %s, old %.4f)' % (p[j], gap[kk, j], d[kk], e[kk, j], ok[kk, j], oc[kk, j]))
# which delta ranges are within 2.35e-4 of binding at p=0.5
j = len(p)-1
sel = d[gap[:, j] > -2.35e-4]
print('delta range within 2.35e-4 at p=0.5:', sel.min(), sel.max())
for pp in (0.48, 0.49):
    jj = np.argmin(abs(p-pp)); sel = d[gap[:, jj] > -2.35e-4]
    print('p', pp, 'range', (sel.min(), sel.max()) if len(sel) else None)
