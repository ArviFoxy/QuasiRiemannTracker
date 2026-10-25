r"""Explicit extremal corner model ("log-periodic resonance").
Y = U^{-m1 (s-a)}.  P(Y) = prod_{j in S} (1 - Y/zeta_j),  zeta_j = k2-th roots of -1/c (|c|=1),
A(Y) = (1 + c Y^{k2}) / P(Y) = prod_{j notin S}(1 - Y/zeta_j)   (polynomial, degree k1 = k2 - d).
L ~ P(Y): plain profile on scales j*m1, j <= d  (max scale d*m1 = m*  <= 1/2).
1/L = A(Y)/(1 + c Y^{k2}): Moebius profile on [0, k1*m1] U [k2*m1, ...] -> exact gap (r*, t*).
Zeros: Re s = a, heights (arg zeta_j + 2 pi k)/(m1 L): d of every k2 sites of a lattice of spacing 2pi/(t* L).
"""
import numpy as np
from common import DELTA

def build(d=5, k2=14, c=1.0, S=None):
    zeta = np.exp(1j*(np.pi + 2*np.pi*np.arange(k2))/k2) * (1/c)**(1/k2)   # roots of 1 + c Y^k2
    S = list(range(d)) if S is None else list(S)
    P = np.poly1d([1.0])
    for j in S: P = P * np.poly1d([-1/zeta[j], 1.0])
    A = np.poly1d([1.0])
    for j in range(k2):
        if j not in S: A = A * np.poly1d([-1/zeta[j], 1.0])
    return zeta, S, P, A

def taylor_inverse(P, n):
    p = P.coeffs[::-1]           # p[0] + p[1] Y + ...
    a = np.zeros(n, dtype=complex); a[0] = 1/p[0]
    for k in range(1, n):
        a[k] = -sum(p[j]*a[k-j] for j in range(1, min(k, len(p)-1)+1))/p[0]
    return a

if __name__ == "__main__":
    mstar = 0.41399
    for (d, k2) in [(5, 14), (9, 25), (14, 39)]:
        m1 = mstar/d; k1 = k2 - d
        zeta, S, P, A = build(d, k2)
        a = taylor_inverse(P, 3*k2)
        print(f"d={d} k2={k2}: m1={m1:.4f}  r=k1*m1={k1*m1:.4f}  t=k2*m1={k2*m1:.4f}  density d*m1/(2pi)={d*m1/(2*np.pi):.5f}")
        print("   |plain coeffs| (scales j*m1):", np.round(np.abs(P.coeffs[::-1]), 3))
        print("   max|Moebius coeff| in gap k1<k<k2:", np.abs(a[k1+1:k2]).max(), " |a_k1|=", round(abs(a[k1]), 3), " |a_k2|=", round(abs(a[k2]), 3),
              " max|a_k| overall:", round(np.abs(a).max(), 3))
    # smoothed finite-window profile at log U = L: residue sum with Gaussian height window
    d, k2 = 5, 14; m1 = mstar/d; k1 = k2 - d
    zeta, S, P, A = build(d, k2)
    dP = P.deriv()
    for L in (200.0, 1000.0):
        rs = np.linspace(0.0, 1.7, 1701)
        F = np.zeros_like(rs, dtype=complex)
        kmax = int(6*m1*L/(2*np.pi)) + 3
        for j in S:
            th = np.angle(zeta[j])           # Y = zeta_j <=> -m1 L (s-a) = i th + 2 pi i k
            for k in range(-kmax*3, kmax*3+1):
                hgt = -(th + 2*np.pi*k)/(m1*L)          # height of zero relative to gamma
                w = np.exp(-hgt**2/2)                   # \hat W(i y): Gaussian window (W(e^v) Gaussian)
                res = 1/(dP(zeta[j]) * (-m1*L) * zeta[j])   # 1/L'(rho) with L = P(Y(s))
                F += w*res*np.exp(1j*rs*L*hgt)
        F *= m1*L/np.sqrt(2*np.pi)      # normalisation so that a band has height ~|a_k|
        gap = (rs > k1*m1 + 0.01) & (rs < k2*m1 - 0.01)
        print(f"L={L:.0f}: |F| at r*={k1*m1:.3f}: {abs(F[np.argmin(abs(rs-k1*m1))]):.3f}, at t*={k2*m1:.3f}: {abs(F[np.argmin(abs(rs-k2*m1))]):.3f}, "
              f"max over gap (r*+0.01,t*-0.01): {np.abs(F[gap]).max():.3e}  (needed: U^-c(r) ~ e^-{0.0294*L:.1f})")
