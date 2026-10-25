# Type I (smooth) slots: A_I(n) = sum_{P primary} w(N(P)/L) N(P)^{-1/2} conj((n/P)_3)   [paper orientation]
# Claim: Poisson in P gives A_I(n) = (L/N)^{1/2} conj(g~(n)) sum_{N(mu) <~ N/L} phi(mu) chi_n(mu), so
#        c_I = g~ A_I lies (numerically) in span{ n -> chi_n(mu) = (mu/n)_3 : N(mu) <= ~N/L } : NO Gauss sum left.
# The other orientation should NOT lie in that span.
# usage: python3 exp_typeI.py K N L Kmu_factor
import sys, os, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zw import *
from build import load
K, N, L = map(int, sys.argv[1:4]); fac = float(sys.argv[4]) if len(sys.argv) > 4 else 3.0
d = load(K, N, L, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'))
Phi = d['Phi'].astype(float); gt = d['gt']; Kp, Np = Phi.shape
ar = Arith(N + 10)
cols = ar.elems(N // 2, N)
assert len(cols) == Np
def all_elems(hi):   # all nonzero elements a + b w with norm <= hi
    out = []
    B = int(math.isqrt(4 * hi // 3)) + 2
    for b in range(-B, B + 1):
        disc = 4 * hi - 3 * b * b
        if disc < 0: continue
        r = math.isqrt(disc)
        for a in range((b - r) // 2 - 1, (b + r) // 2 + 2):
            nn = a * a - a * b + b * b
            if 0 < nn <= hi: out.append((a, b, nn))
    return np.array(out, dtype=np.int64)
def chi_n_of(c, E):
    """chi_n(mu) = prod_{pi | n} (mu/pi)_3 for an array E of elements mu = (a,b); 0 if not coprime"""
    v = np.ones(len(E), complex)
    for p, r in zip(c['ps'], c['rs']):
        t = ar.cubtab(p, r)[(E[:, 0] + E[:, 1] * r) % p]
        v *= np.where(t < 0, 0, W ** np.where(t < 0, 0, t))
    return v
# slot elements: all primary P with N(P) <= 4L, smooth weight
Pe = all_elems(int(6 * L)); Pe = Pe[(Pe[:, 0] % 3 == 2) & (Pe[:, 1] % 3 == 0)]
wP = np.exp(-np.pi * Pe[:, 2] / L)          # Gaussian slot weight (Fourier dual: Gaussian, N(mu) <~ 27 N/L)
# dual elements mu: all elements with N(mu) <= fac * N/L  (units included: supplementary laws)
Kmu = int(fac * 27 * N / L)
Me = all_elems(Kmu)
print(f'K={K} N={N} L={L}: N\'={Np} K\'={Kp}; slots: {len(Pe)} primary P (N(P)<=4L, smooth bump at L); dual mu: {len(Me)} elements N(mu)<={Kmu}')
A_paper = np.zeros(Np, complex); A_other = np.zeros(Np, complex)
Psi = np.zeros((Np, len(Me)), complex)
for j, c in enumerate(cols):
    x = chi_n_of(c, Pe[:, :2])                # (P/n)_3 = (n/P)_3 by cubic reciprocity
    A_paper[j] = np.sum(wP * np.conj(x)); A_other[j] = np.sum(wP * x)
    Psi[j] = chi_n_of(c, Me[:, :2])
U_, s_, _ = np.linalg.svd(Psi, full_matrices=False)
rk = int(np.sum(s_ > 1e-8 * s_[0])); Q = U_[:, :rk]          # orthonormal basis of the column space
def frac(v): return np.sum(np.abs(Q.conj().T @ v) ** 2) / np.sum(np.abs(v) ** 2)
cI = gt * A_paper; cO = gt * A_other
print(f'  span of {rk} cubic-character columns: dim/N\' = {rk/Np:.3f}')
print(f'  fraction of c_I = g~ * A_paper   in cubic span: {frac(cI):.6f}')
print(f'  fraction of     g~ * A_other     in cubic span: {frac(cO):.4f}')
print(f'  fraction of     A_paper alone    in cubic span: {frac(A_paper):.4f}')
rnd = np.exp(2j*np.pi*np.random.default_rng(1).random(Np))
print(f'  fraction of random phases        in cubic span: {frac(rnd):.4f}')
# P1 for Type I slots: ||Phi c_I||^2 / Diag
for nm, c in [('c_I (paper orientation)', cI), ('other orientation', cO)]:
    S = np.sum(np.abs(Phi @ c) ** 2); dg = np.sum((Phi ** 2) @ np.abs(c) ** 2)
    print(f'  {nm:26s} ||Phi c||^2/Diag = {S/dg:.3f}   (allowance {(Kp+Np)*np.sum(np.abs(c)**2)/dg:.1f})')
# principal angles between V2 (quadratic, K') and V3 = cubic span restricted to N(mu) <= K
QV, _ = np.linalg.qr(Phi.T)
cos = np.linalg.svd(QV.conj().T @ Q, compute_uv=False)
print(f'  principal angles quad span (dim {Kp}) vs cubic span (dim {rk}): max cos^2={cos[0]**2:.4f} '
      f'(random-subspace edge {(math.sqrt(Kp/Np)+math.sqrt(rk/Np))**2:.4f}); mean cos^2={np.mean(cos**2):.4f} (K\'/N\'={Kp/Np:.4f})')
