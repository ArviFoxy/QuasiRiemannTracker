"""What moves the count face: theta* of the merged return when the continuous ODE shape is changed.

 (a) kappa + dk  : a uniformly stronger density step (target point (kappa, kappa) raised by dk);
 (b) boot face   : the native line (B = 0.99999, slope 0) continued below 5143/2000 before the ODE starts;
 (c) floor q < 1/2: the ODE continued past the density floor with the same closed-form kappa(q).
Count face = best curve face for the count (scanned), physical face = best curve face for the capacity.
[numerical; the shapes in (a)-(c) are hypothetical, nothing here is proven]"""
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, minimize_scalar
from common import best_theta, MERGED, CC0
d = 0.999
y2, dp = 2 * 69313573 / 150000000, 0.8044451001


def q_of(B, L, qcap=0.75):
    return min(d * L / (6 * B - L), qcap)


def kappa(q):
    return 4 * (5 - 3 * q) / (25 - 18 * q)


def curve(L0, B0, dk=0.0, Lend=1.70):
    f = lambda L, y: [(y[0] - (kappa(q_of(y[0], L)) + dk)) / (L - (kappa(q_of(y[0], L)) + dk))]
    sol = solve_ivp(f, [L0, Lend], [B0], method='DOP853', rtol=1e-12, atol=1e-14, dense_output=True)
    return lambda L: float(sol.sol(L)[0])


def evaluate(Bc, Lq, Lhi):
    """count face: scan the curve on [Lq, Lhi] for the least theta*; physical face: max capacity"""
    cap = lambda L: (y2 - (2 - Bc(L)) * dp) / L
    Lp = minimize_scalar(lambda L: -cap(L), bounds=(max(Lq, 2.0), min(Lhi, 2.5)), method='bounded').x
    pB, pL = Bc(Lp), Lp
    # the count value of a face is about B - 0.093 L (iso-theta direction); scan coarsely then refine
    Ls = np.linspace(Lq, min(Lhi, Lq + 0.25), 6)
    vals = [(best_theta(Bc(L), L, CC0, pB, pL), L) for L in Ls]
    vals = [(v, L) for v, L in vals if v is not None]
    (t, cand, m, z), L = min(vals, key=lambda x: x[0][0])
    return float(t), cand, L, Bc(L), float(m), float(z), pL, pB


if __name__ == '__main__':
    Lq_of = lambda Bc, qs, lo, hi: brentq(lambda L: d * L / (6 * Bc(L) - L) - qs, lo, hi)
    print('(a) kappa + dk  (boot (0.99999, 2.5715), stop at q = 1/2)')
    for dk in (0.0, 0.005, 0.01, 0.02):
        Bc = curve(2.5715, 0.99999, dk)
        Lq = Lq_of(Bc, 0.5, 1.75, 2.5)
        t, cand, L, B, m, z, pL, pB = evaluate(Bc, Lq, 2.5715)
        print('  dk=%.3f  q=1/2 at L=%.5f  count face (B=%.6f, L=%.5f) %-4s witness m=%.4f z=%.4f  theta*=%.10f  %+.3e'
              % (dk, Lq, B, L, cand, m, z, t, t - float(MERGED)))
    print('(b) boot face (0.99999, Lb): native line continued to Lb')
    for Lb in (2.5715, 2.5, 2.4, 2.3, 2.2):
        Bc = curve(Lb, 0.99999)
        Lq = Lq_of(Bc, 0.5, 1.75, Lb)
        t, cand, L, B, m, z, pL, pB = evaluate(Bc, Lq, Lb)
        print('  Lb=%.4f  q=1/2 at L=%.5f  count face (B=%.6f, L=%.5f) %-4s witness m=%.4f z=%.4f  theta*=%.10f  %+.3e'
              % (Lb, Lq, B, L, cand, m, z, t, t - float(MERGED)))
    print('(c) ODE past the floor (same kappa(q)), stop at q_stop')
    Bc = curve(2.5715, 0.99999)
    for qs in (0.5, 0.48, 0.45, 0.42, 0.40):
        Lq = Lq_of(Bc, qs, 1.5, 2.5)
        t, cand, L, B, m, z, pL, pB = evaluate(Bc, Lq, 2.5715)
        print('  q_stop=%.2f  at L=%.5f  count face (B=%.6f, L=%.5f) %-4s witness m=%.4f z=%.4f  theta*=%.10f  %+.3e'
              % (qs, Lq, B, L, cand, m, z, t, t - float(MERGED)))
