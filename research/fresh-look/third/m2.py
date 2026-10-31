# separate count face and physical face; price density-step faces for the count only
import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
import numpy as np, worth, fast, ideal
from ideal import face_count
fast.branch = worth.make_branch(5/6); ideal.branch = fast.branch
d = np.round(np.arange(0.30, 0.60, 0.0005), 6)
p = np.round(np.array([0.45, 0.48, 0.49, 0.495, 0.499, 0.5]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')
def theta(Bc, Lc, Bp, Lp, h=0.8097, numCap=0.075, capc=None, reserve=1e-8, shift=0.0):
    if capc is None: capc = 0.1 + 0.06*(5143/2000 - Lc)
    ok, v = face_count(DD, PP, Bc, Lc, capc)
    env = np.where(ok, v, np.inf)
    lo, hi = 0.86, 0.885
    for _ in range(50):
        th = (lo+hi)/2; c = 1-th; ell = 4*c-1/3; y = h-2*ell; kappa = 1-2*c; dd = h+1e-10
        C = min(numCap*dd, (2*y-(2-Bp)*dd)/Lp)
        e = np.minimum(env, worth.old_count(DD, PP, kappa, 5/6)) - shift
        E = 0.5+13*h/75-y/2-ell/2-0.09*dd+DD/2+DD*PP*(ell-C/2)+0.75*dd*e
        if E.max() > th-reserve: lo = th
        else: hi = th
    return hi
base = theta(0.99999, 2.0001, 0.99999, 2.0001)
print('base %.8f' % base)
for sig in (0.111, 0.093, 0.08, 0.05, 0.0):
    for dL in (0.05, 0.1, 0.2):
        t = theta(0.99999 - sig*dL, 2.0001 - dL, 0.99999, 2.0001)
        print('count face along slope %.3f, dLambda %.2f: theta %.8f  d %+.2e' % (sig, dL, t, t - base))
# count face alone vs physical alone
for L in (1.97, 1.95, 1.9):
    print('count only Lambda %.2f: %+.2e   physical only: %+.2e' % (L, theta(0.99999, L, 0.99999, 2.0001) - base, theta(0.99999, 2.0001, 0.99999, L) - base))
