#!/usr/bin/env python3
"""
Conditional Guth-Maynard (cubic-trace) line inserted into the detector LP.

GM (Lemma 4.2 analogue):  R <~ Y^{1-d} + Y^{-d} (3 Y E2 + S3)^{1/3},
  E2 = sum_{u!=v in R} |G(u,v)|^2,  S3 = tr(O^3).
Hypotheses (NOT available):
  (H1) width-1 coset 4th moment: sum_{v~U} |sum_{n~Y} psi_u psibar_v(n)|^4 << U^{1+eps} Y^2
       => E2 <= R^{3/2} U^{1/2} Y   (Hoelder over v in R)
  (H2') |S3 - R^3 sum w^6| <= R^3 Y^{3d - eta}   (power saving over Schatten E2^{3/2})
Then  rho <= GM(y) = y (4-6d)/3 + a,  a = 1/3 under (H1)  [a = 2/3 with the proved width-2 moment],
valid only when y >= rho (rank non-degenerate: rows <= columns).
"""
import numpy as np

def lp(d, p, B, Lam, gm_a=None, slot_free=False, tgrid=np.linspace(1, 1.5, 501)):
    I = lambda r: 1 - d*(p + (1-p)*r)
    P = lambda m: 1 - 2*d*m - 2*d*p*(B - 2*m)/Lam if p > 0 else 1 - 2*d*m
    L = lambda t: 1/6 + (5/6 - d)*t
    def GM(y, cnt):  # line valid only if y >= cnt; else +inf
        if gm_a is None: return np.inf
        v = y*(4 - 6*d)/3 + gm_a
        return v if y >= v - 1e-12 else np.inf
    best = (9, None)
    for t in tgrid:
        worst = L(t)
        for r in np.linspace(max(t - 0.5, 0), min(1.0, t), 301):
            m = t - r
            c = min(I(r), P(m))
            # GM on Moebius block, plain block, S^2, product M S (length r+m)
            for y in [r, m, 2*m, r + m]:
                c = min(c, GM(y, c))
            worst = max(worst, c)
        if worst < best[0]: best = (worst, t)
    R = best[0]
    if slot_free and gm_a is not None:
        # saturated slot products of free length y>=rho: fixed point of GM
        fp = gm_a/(1 - (4 - 6*d)/3)
        R = min(R, fp)
    return R, best[1]

if __name__ == "__main__":
    d, p, B, Lam = 0.4546, 0.5, 0.95311, 2.6
    print("marked corner, no GM:          ", lp(d, p, B, Lam))
    print("marked, GM proved (a=2/3):      ", lp(d, p, B, Lam, gm_a=2/3, slot_free=True))
    print("marked, GM (H1)+(H2') witnesses only:", lp(d, p, B, Lam, gm_a=1/3))
    print("marked, GM (H1)+(H2') + free slot products:", lp(d, p, B, Lam, gm_a=1/3, slot_free=True))
    for nu in [0.45, 0.5, 0.51]:
        rho = 1 - 10*nu/(15 - 6*nu)
        print(f"nu={nu}: rho={rho:.4f}  unmarked+GM proved: {lp(nu, 0, 1, 1, gm_a=2/3)[0]:.4f}  "
              f"unmarked+GM(H1)(H2'): {lp(nu, 0, 1, 1, gm_a=1/3)[0]:.4f}")
