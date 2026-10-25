r"""Does the single-row adversary also cover the high-side numerator?

The return's numerator is a plain sum of length n0 = 2l/h = 0.418 (U units), slightly longer than the
count corner's plain length m* = 0.414.  Hoelder is tight only if the binding rows have
|S_{n0}|^2 ~ U^{delta n0 - 0.0015} (from R + 2 delta n0 + 2 q z_A = 1.003).  A resonance row with plain
profile ending exactly at m* has nothing at scale n0, so its numerator is a power below that level.
Test: L = P(Y) (1 + eps Y^{j0}), j0 m1 = n0 - m*, eps = U^{-0.00075}.  Then
  * the plain profile reaches n0 at level eps (Hoelder-critical);
  * 1/L = A/(1 + c Y^{k2}) * sum_k (-eps)^k Y^{k j0}: the Moebius gap (r*, t*) is filled only at level
    eps^k at r* + k(n0 - m*); it must stay below the tent U^{-c(r)}, c(r) = (R - Lin(r))/2;
  * the new zeros (1 + eps Y^{j0} = 0) lie at Re s = a - 0.00075/(n0 - m*) < a.
The script checks the Moebius profile against the tent for several log U.
"""
import numpy as np
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fine_resonance import beatty_roots, coeffs_by_fft
from math import gcd

DELTA, P_AMP = 0.4546, 0.5
MSTAR, TSTAR, RSTAR, R = 0.41399, 1.15527, 0.74128, 0.604207
N0 = 0.418


def lin(r):
    return np.where(r <= 1.0, 1 - DELTA*(P_AMP + (1 - P_AMP)*r), 1/6 + (5/6 - DELTA)*r)


def tent(r):
    return np.maximum(0.0, 0.5*(R - lin(r)))


def check(d, logU):
    k2 = int(round(d*TSTAR/MSTAR))
    while gcd(k2, d) != 1:
        k2 += 1
    k1 = k2 - d
    m1 = MSTAR/d
    j0 = max(1, int(round((N0 - MSTAR)/m1)))
    eps = np.exp(-0.00075*logU)
    zeta, S, notS = beatty_roots(d, k2)
    A = coeffs_by_fft(zeta[notS], k1)                     # Moebius profile of 1/P on [0, r*]
    nmax = 2*k2
    inv_P = np.zeros(nmax, dtype=complex)                   # 1/P = A/(1 + c Y^k2), c = 1
    for q in range(0, nmax//k2 + 1):
        for j, a in enumerate(A):
            n = j + q*k2
            if n < nmax:
                inv_P[n] += a*(-1.0)**q
    geo = np.zeros(nmax, dtype=complex)                     # 1/(1 + eps Y^j0)
    for k in range(0, nmax//j0 + 1):
        if k*j0 < nmax:
            geo[k*j0] = (-eps)**k
    inv_L = np.convolve(inv_P, geo)[:nmax]
    r = np.arange(nmax)*m1
    gap = (r > RSTAR + 1e-9) & (r < TSTAR - 1e-9)
    # log_U of |coefficient| (saturation = 0); must be <= -tent(r) inside the gap
    with np.errstate(divide='ignore'):
        lg = np.log(np.abs(inv_L) + 1e-300)/logU
    worst = np.max(lg[gap] + tent(r[gap]))
    at_t = np.abs(inv_L[np.argmin(np.abs(r - TSTAR))])
    at_r = np.abs(inv_L[np.argmin(np.abs(r - RSTAR))])
    return j0, eps, worst, at_r, at_t


if __name__ == "__main__":
    print("dip margin = max over (r*, t*) of [log_U|M_r| + tent(r)]  (must be <= 0)")
    for d in (400, 1600):
        for logU in (2e3, 1e4, 1e5):
            j0, eps, worst, at_r, at_t = check(d, logU)
            print(f"  d={d:5d} logU={logU:8.0f} j0={j0:3d} eps={eps:.3e}  dip margin={worst:+.5f}  "
                  f"|M| at r*={at_r:.3f}  at t*={at_t:.3f}")


def analytic_margin(D=0.00075, Delta=N0 - MSTAR, npts=20001):
    """Exact version (no floating floor).  In the gap the smallest power of eps reaching scale r is
    k = ceil((r - r*)/Delta), with |coeff| <= U^{-D k} (A-coefficients are <= 1).  Dip margin =
    max_r [ -D*ceil((r - r*)/Delta) + tent(r) ] over (r*, t*); must be <= 0."""
    r = np.linspace(RSTAR + 1e-9, TSTAR - 1e-9, npts)
    k = np.ceil((r - RSTAR)/Delta)
    return np.max(-D*k + tent(r)), D/Delta, DELTA*(1 - P_AMP)/2


if __name__ == "__main__":
    m, slope_pert, slope_tent = analytic_margin()
    print(f"analytic: dip margin = {m:+.6f} (<= 0 means the perturbed row keeps the corner); "
          f"perturbation decay {slope_pert:.4f} per unit r vs tent slope {slope_tent:.4f}")
    # same-face identity: D/Delta = delta(1 - 2p/Lambda)/2 vs tent slope delta(1-p)/2  <=>  Lambda > 2
    for Lam in (2.0, 2.5, 2.9, 3.0):
        print(f"  same-face value D/Delta = {DELTA*(1 - 2*P_AMP/Lam)/2:.4f} at Lambda={Lam} (tent {slope_tent:.4f})")
