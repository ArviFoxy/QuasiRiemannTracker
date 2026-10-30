# Price a uniform count shift (and DH) in the worth.py float model (newTop row only).
import numpy as np, worth as W, fast, ideal
from ideal import face_count
def theta_star_shift(shift=0.0, dh=False, L=401/200, B=0.99999, h=0.8001361, numCap=0.075, reserve=1e-8, LONG=5/6):
    cap = 0.1 + 0.06*(5143/2000 - L)
    fast.branch = W.make_branch(LONG); ideal.branch = fast.branch
    ok, v = face_count(W.DD, W.PP, B, L, cap)
    env = np.where(ok, v, np.inf)
    lo, hi = 0.85, 0.885
    for _ in range(50):
        th = (lo+hi)/2; c = 1-th; ell = 4*c-1/3; y = h-2*ell; kappa = 1-2*c; dd = h+1e-10
        C = min(numCap*dd, (2*y-(2-B)*dd)/L)
        e = np.minimum(env, W.old_count(W.DD, W.PP, kappa, LONG)) - shift
        if dh: e = 1 - W.DD
        E = 0.5+13*h/75-y/2-ell/2-0.09*dd+W.DD/2+W.DD*W.PP*(ell-C/2)+0.75*dd*e
        if E.max() > th-reserve: lo = th
        else: hi = th
    k = np.unravel_index(np.argmax(E), E.shape)
    return hi, W.DD[k], W.PP[k], e[k]
b = theta_star_shift()
print('base', b)
for s in (0.0005, 0.001, 0.0024, 0.005, 0.01, 0.02):
    t = theta_star_shift(s); print('shift %.4f: theta %.8f dtheta %+.2e bind d %.4f p %.3f count %.5f' % ((s, t[0], t[0]-b[0]) + t[1:]))
t = theta_star_shift(dh=True); print('DH: theta %.8f dtheta %+.2e bind d %.4f p %.3f' % (t[0], t[0]-b[0], t[1], t[2]))
