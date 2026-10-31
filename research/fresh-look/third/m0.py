import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
import numpy as np, worth, fast, ideal
from ideal import face_count
B, L, h = 0.99999, 2.0001, 0.8097
cap = 0.1 + 0.06*(5143/2000 - L)
fast.branch = worth.make_branch(5/6); ideal.branch = fast.branch
d = np.array([0.426]); p = np.array([0.5])
ok, v = face_count(d, p, B, L, cap)
th = 0.873382278649624; c = 1-th; kappa = 1-2*c
print('face count ok', ok, v, 'old', worth.old_count(d, p, kappa, 5/6))
# landscape E(delta) at p=1/2 and p=0.45
DD, PP = worth.DD, worth.PP
ok, v = face_count(DD, PP, B, L, cap)
env = np.where(ok, v, np.inf)
ell = 4*c - 1/3; y = h - 2*ell; dd = h + 1e-10
C = min(0.075*dd, (2*y - (2-B)*dd)/L)
e = np.minimum(env, worth.old_count(DD, PP, kappa, 5/6))
E = 0.5 + 13*h/75 - y/2 - ell/2 - 0.09*dd + DD/2 + DD*PP*(ell - C/2) + 0.75*dd*e
print('C', C, 'ell', ell, 'y', y, 'x', 1+ell-h)
for j, pp in enumerate(worth.p):
    k = np.argmax(E[:, j]); print('p %.3f: max E %.8f at delta %.4f  (th %.8f)  count %.5f old %.5f' % (pp, E[k, j], DD[k, j], th, e[k, j], worth.old_count(DD[k,j], pp, kappa, 5/6)))
# E profile along delta at p = 0.5
j = list(worth.p).index(0.5)
for dl in (0.38, 0.40, 0.41, 0.42, 0.426, 0.43, 0.44, 0.45, 0.46, 0.48, 0.50, 0.52, 0.55, 0.6):
    k = np.argmin(abs(DD[:, j]-dl)); print('delta %.3f E-th %+.3e count %.5f env %.5f old %.5f' % (DD[k,j], E[k,j]-th, e[k,j], env[k,j], worth.old_count(DD[k,j], 0.5, kappa, 5/6)))
