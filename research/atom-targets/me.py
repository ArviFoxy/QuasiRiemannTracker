import sys, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/atom-targets')
import targets as T

def geometry_eps(theta, P):
    h, cg, eps = P['h'], P['cg'], P.get('eps', 0.0)
    l = (2*h - 1 + eps - (theta - 5/6 - (1 - h)/6)/cg)/3
    x = 1 + l - h; y = h - 2*l + eps; kap = 2*theta - 1
    return l, x, y, kap

T.geometry = geometry_eps
P0 = dict(T.BASE)
dl, pp = np.meshgrid(np.linspace(0.30, 0.75, 226), np.linspace(0.30, 0.5, 21), indexing='ij')
R = T.count(dl, pp, P0)
def th(P):
    lo, hi = 0.8740, 0.8752
    for _ in range(40):
        mid = (lo+hi)/2
        if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
        else: lo = mid
    return hi
b = th(P0); print('base', b)
for eps in (1e-4, 3e-4, 1e-3):
    P = dict(P0); P['eps'] = eps
    t = th(P); print('eps', eps, 'theta', t, 'dtheta', t-b, 'dtheta/eps', (t-b)/eps)
