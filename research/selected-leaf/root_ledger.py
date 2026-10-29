"""E5b. Does the selected-norm leaf survive the sixth-root sum?  [numerical, derived model]

Rows of the packed leaf are z = u r^6 (u sixth-free).  PR 93's selected norm is per root r: for the cores u
at root r (norm <= Y_r = Z^{M - 6 rho}, rho = log_Z N(r)) and any source family of norm <= X it gives
X + Y_r^{1-delta} X^delta.  The X term does not decay with r, and there are ~Z^rho roots of size rho, so the
selected energy is Z^{E_sel} with E_sel = max_rho [ rho + max(X_eff, (1-delta) y + delta X_eff) ], y = M - 6 rho.

Variants of X_eff (log of the source length the norm sees at root rho):
  'plain'   : X_eff = P + s (today's polynomial; no use of the plain sums' structure)
  'pv'      : pointwise Polya-Vinogradov on the plain sums, norm on the slots only:
              per root  2*min(x, y - x) + max(s, (1-delta) y + delta s)   (min with 'plain' per root)
  'dual'    : the plain sums dualized inside the norm (I-side Poisson): X_eff = sum_i min(x_i, y - x_i) + s
A root contributes nothing when y < x_i for some i (the smooth sum is longer than the conductor).

The ledger (Sil, StepData.LedgerAt): for every side geometry, price <= u (+ eps/16).  Here
price = max(price_sel, K * deletionNeed) with price_sel = E_sel - M, K = 1/2 + eta.
Geometry: S in [0, c], f = cg = 0 (worst), PC + L S <= B, u = a w, s <= w - u, t in [0, 1 + 6u], H = 1 + t - 6u,
plain split x1 = x2 = PC/2 (worst for the dilution) and also x1 = PC, x2 = 0.
"""
import numpy as np

DELTA = 0.5


def deletion_need(B0, L0, c0, P, s, M):
    return max(0.0, min(s, max(s - c0 * M, (P + L0 * s - B0 * M) / L0)))


def e_sel(variant, x1, x2, s, M, nrho=601):
    P = x1 + x2
    best = -1e9
    for rho in np.linspace(0.0, M / 6, nrho):
        y = M - 6 * rho
        if variant != 'plain' and (y < x1 or y < x2):
            continue                      # rapid decay of a plain sum: the root contributes nothing
        full = max(P + s, (1 - DELTA) * y + DELTA * (P + s))
        if variant == 'plain':
            per = full
        elif variant == 'pv':
            pv = (min(x1, y - x1) + min(x2, y - x2)) + max(s, (1 - DELTA) * y + DELTA * s)
            per = min(full, pv)
        elif variant == 'dual':
            xe = min(x1, y - x1) + min(x2, y - x2) + s
            per = max(xe, (1 - DELTA) * y + DELTA * xe)
        best = max(best, rho + per)
    return best


def worst(variant, B, L, c, a, B0, L0, c0, K, nS=21, nt=7):
    """max over the side geometry of price - u"""
    worst_v, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        w = S
        u = a * w
        PCmax = B - L * S
        for PC in (PCmax, 0.75 * PCmax, 0.5 * PCmax):
            for s in (w - u, 0.5 * (w - u)):
                for t in np.linspace(0.0, 1 + 6 * u, nt):
                    M = 1 + t - 6 * u
                    for (x1, x2) in ((PC / 2, PC / 2), (PC, 0.0)):
                        ps = e_sel(variant, x1, x2, s, M) - M
                        pd = K * deletion_need(B0, L0, c0, PC, s, M)
                        v = max(ps, pd) - u
                        if v > worst_v:
                            worst_v, where = v, dict(S=round(S, 4), PC=round(PC, 4), s=round(s, 4), t=round(t, 3),
                                                     x=(round(x1, 3), round(x2, 3)), sel=round(ps - u, 5),
                                                     dele=round(pd - u, 5))
    return worst_v, where


if __name__ == '__main__':
    import sys
    sys.path.insert(0, '.')
    from native_line import run
    K = 0.5 + 1e-3
    Lend, cend, reason, path = run(K)
    print('native line K=%.4f ends at L=%.5f cap %.4f (%s)' % (K, Lend, cend, reason), flush=True)
    for Lq in (2.6, 2.4, 2.2, 2.1, 2.05):
        i = min(range(len(path)), key=lambda j: abs(path[j][0] - Lq))
        L, c, a = path[i]
        L0, c0, _ = path[i - 1]
        for variant in ('plain', 'pv', 'dual'):
            v, where = worst(variant, 0.99999, L, c, a, 0.99999, L0, c0, K)
            print('L=%.4f c=%.4f a=%.2e  %-5s  max(price - u) = %+.5f  %s' % (L, c, a, variant, v, where), flush=True)
