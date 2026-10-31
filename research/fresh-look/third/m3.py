# continuum marked density chain from the native end, past the floor (optimistic: closed-form slope, no cap / reference limits)
import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
import numpy as np
from m2 import theta
def kap(q): return 4*(5-3*q)/(25-18*q)
def curve(B0=0.99999, L0=2.0001, Lend=1.6, n=4000):
    Ls = np.linspace(L0, Lend, n); B = B0; out = [(L0, B0, None, None)]
    for i in range(1, n):
        L = Ls[i-1]; q = 0.999*L/(6*B-L); k = kap(q); s = (B-k)/(L-k)
        B = B + s*(Ls[i]-L); out.append((Ls[i], B, q, s))
    return out
cv = curve()
base = theta(0.99999, 2.0001, 0.99999, 2.0001)
for L, B, q, s in cv[::400]:
    if q is None: continue
    t = theta(B, L, 0.99999, 2.0001, capc=0.1342894)
    print('L %.4f B %.6f q %.4f slope %.4f  count-face-only theta %.8f  d %+.2e' % (L, B, q, s, t, t-base))
