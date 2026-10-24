"""Direct (fixed-face) effect of the same atoms, using the base chain's faces, to separate chain feedback."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/atom-targets')
import targets as T
c = float(sys.argv[1]); epsL = float(sys.argv[2])
P = dict(T.BASE)
P.update(BC=0.9560923431685, LC=2.8966178970586, BP=0.9607555161997, LP=3.0092583268338, sI=c, epsL=epsL)
dl, pp = np.meshgrid(np.linspace(0.30, 0.75, 226), np.linspace(0.30, 0.5, 21), indexing='ij')
R = T.count(dl, pp, P)
lo, hi = 0.8735, 0.8755
for _ in range(40):
    mid = (lo+hi)/2
    if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
    else: lo = mid
print(f"DIRECT c={c} epsL={epsL} theta*={hi:.8f}", flush=True)
