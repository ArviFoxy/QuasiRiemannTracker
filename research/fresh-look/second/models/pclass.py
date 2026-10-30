# Value of a class-refined count: improve the count only for rows with slot amplitude p >= p0.
# Uses the opus_fresh float model (worth.py machinery, newTop row).  [numerical, float model]
import sys, numpy as np
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'base_models'))
import fast, ideal, worth as W
from ideal import face_count
d = np.round(np.arange(0.30, 0.65, 0.001), 6)
p = np.round(np.concatenate([np.arange(0.30, 0.49, 0.01), [0.49, 0.495, 0.499, 0.5]]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')
def theta_star(mod=None, L=401/200, B=0.99999, h=0.8001361, numCap=0.075, reserve=1e-8, LONG=5/6):
    cap = 0.1 + 0.06*(5143/2000 - L)
    fast.branch = W.make_branch(LONG); ideal.branch = fast.branch
    ok, v = face_count(DD, PP, B, L, cap)
    env = np.where(ok, v, np.inf)
    lo, hi = 0.85, 0.885
    for _ in range(50):
        th = (lo+hi)/2; c = 1-th; ell = 4*c-1/3; y = h-2*ell; kappa = 1-2*c; dd = h+1e-10
        C = min(numCap*dd, (2*y-(2-B)*dd)/L)
        e = np.minimum(env, W.old_count(DD, PP, kappa, LONG))
        if mod is not None: e = mod(e)
        E = 0.5+13*h/75-y/2-ell/2-0.09*dd+DD/2+DD*PP*(ell-C/2)+0.75*dd*e
        if E.max() > th-reserve: lo = th
        else: hi = th
    k = np.unravel_index(np.argmax(E), E.shape)
    return hi, DD[k], PP[k], e[k]
if __name__ == "__main__":
  b = theta_star(); print('base theta %.8f bind d %.3f p %.3f count %.5f' % b)
  for p0 in (0.499, 0.49, 0.48, 0.45, 0.40, 0.35):
      for lab, f in (('DH', lambda e: np.where(PP >= p0, np.minimum(e, 1-DD), e)),
                   ('-0.01', lambda e: np.where(PP >= p0, e-0.01, e))):
          t = theta_star(f)
          print('p0 %.3f %-5s: theta %.8f dtheta %+.2e bind d %.3f p %.3f' % (p0, lab, t[0], t[0]-b[0], t[1], t[2]))
