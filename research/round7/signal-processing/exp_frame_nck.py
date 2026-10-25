# (1) frame bounds of the quadratic dictionary: singular values of Phi (K' x N'), sigma^2/N'
# (2) matrix-concentration (NCK) check: S = sum_n beta(n) phi_n x_n^T.  Compare ||S||_op^2 for
#     beta = g~ (true), beta = g~ with an independent random phase per multiplicative block
#     {n : largest prime factor = pi}, and fully random phases; and the NCK variance proxy
#     sigma^2 = max(||sum_n |beta|^2 ||x_n||^2 phi_n phi_n^T||, ||sum_n ||phi_n||^2 conj(x_n) x_n^T||).
# usage: python3 exp_frame_nck.py K N L
import sys, os, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from build import load
W3 = np.exp(2j * np.pi / 3)
K, N, L = map(int, sys.argv[1:4])
d = load(K, N, L, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'))
Phi = d['Phi'].astype(float); gt = d['gt']; Xe = d['Xe']; colps = d['colps']
Kp, Np = Phi.shape; Lp = Xe.shape[1]
X = np.where(Xe < 0, 0, np.conj(W3 ** np.where(Xe < 0, 0, Xe)))     # paper orientation conj((n/P)_3)
s = np.linalg.svd(Phi, compute_uv=False) ** 2 / Np
print(f'K={K} N={N} L={L}: K\'={Kp} N\'={Np} L\'={Lp}')
print(f'  frame bounds of quadratic rows: sigma^2/N\' in [{s.min():.3f}, {s.max():.3f}], quartiles {np.percentile(s,[25,50,75]).round(3)}')
sig2 = max(np.linalg.norm((Phi * (np.sum(np.abs(X) ** 2, 1))[None, :]) @ Phi.T, 2),
           np.linalg.norm((X.conj().T * np.sum(Phi ** 2, 0)[None, :]) @ X, 2))
rng = np.random.default_rng(5)
lpf = np.array([max(eval(p)) for p in colps])                        # largest rational prime below the block
blocks = {p: rng.random() for p in np.unique(lpf)}
bph = np.exp(2j * np.pi * np.array([blocks[p] for p in lpf]))
def op2(beta): return np.linalg.norm(Phi @ (beta[:, None] * X), 2) ** 2
for nm, b in [('true g~', gt), ('g~ x random phase per block (largest prime)', gt * bph),
              ('fully random phases', np.exp(2j * np.pi * rng.random(Np)))]:
    print(f'  {nm:44s} ||S||_op^2 / sigma^2 = {op2(b)/sig2:.3f}   ||S||_op^2/(N\'K\') = {op2(b)/(Np*Kp):.3f}')
print(f'  NCK proxy sigma^2/(N\'K\') = {sig2/(Np*Kp):.3f};  large-sieve product (K\'+N\')(N\'+L\')/(N\'K\') = {(Kp+Np)*(Np+Lp)/(Np*Kp):.1f}')
