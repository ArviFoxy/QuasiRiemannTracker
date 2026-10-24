import sys, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/atom-targets')
import targets as T
P0 = dict(T.BASE)
dl, pp = np.meshgrid(np.linspace(0.30, 0.75, 226), np.linspace(0.30, 0.5, 21), indexing='ij')
def th(P):
    R = T.count(dl, pp, P)
    lo, hi = 0.8700, 0.8760
    for _ in range(40):
        mid = (lo+hi)/2
        if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
        else: lo = mid
    return hi
b = th(P0); print('base', b, flush=True)
for (BC, LC, BP, LP, cap) in [(1.0, 2.0, 0.9610063016, 3.0106108488, 13/250), (0.9564652291, 2.9005114226, 1.0, 2.0, 13/250), (1.0, 2.0, 1.0, 2.0, 0.2), (0.9564652291, 2.85, 0.9610063016, 2.95, 13/250)]:
    P = dict(P0); P.update(BC=BC, LC=LC, BP=BP, LP=LP, capC=cap)
    if BP == 1.0: P['sP'] = 0.2
    t = th(P); print(f'BC={BC} LC={LC} BP={BP} LP={LP}: theta*={t:.7f} dtheta={t-b:+.3e}', flush=True)
