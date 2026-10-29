"""Question 6: the chain as a Legendre envelope, and its continuum limit.

(1) Exact (fractions): for the 130 faces of research/chain/steps_f050_dL200.json
    * crossings s_k = (B_{k-1} - B_k)/(Lam_{k-1} - Lam_k) equal the step field `s0` (rounded) and are strictly increasing,
      so every face is active on [s_k, s_{k+1}] and the envelope E is convex, piecewise linear;
    * on that piece E(s) = B_k - Lam_k s, hence Lam_k = -E'(s), B_k = E(s) - s E'(s) (Legendre), and
      dB/dLam = s_k exactly in the discrete sense (definition of the crossing).
(2) Float: comparison with the continuum ODE dB/dL = s0(B, L) of research/newpowers/ta/ode2.py
    (q = 0.999 L/(6B - L), v = 0 marked HIGH gate, parent = current face).  Not run by default (slow);
    pass --ode.
"""
import os, sys, time
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from faces import load_faces


def exact_checks():
    steps, F = load_faces()
    s = [None] + [(F[k - 1][0] - F[k][0]) / (F[k - 1][1] - F[k][1]) for k in range(1, len(F))]
    dev = max(abs(float(s[k]) - steps[k - 1]['s0_float']) for k in range(1, len(F)))
    inc = all(s[k] < s[k + 1] for k in range(1, len(F) - 1))
    dL = {F[k - 1][1] - F[k][1] for k in range(1, len(F))}
    print(f'crossings: s_1 = {float(s[1]):.6f} ... s_129 = {float(s[-1]):.6f};  max |s_k - s0_float| = {dev:.2e};'
          f'  strictly increasing: {inc};  dLam values: {sorted(float(x) for x in dL)}')
    # Legendre on every piece: at the midpoint of [s_k, s_{k+1}] the active face is k (exact check)
    bad = 0
    for k in range(1, len(F) - 1):
        sm = (s[k] + s[k + 1]) / 2
        vals = [(B - L * sm, j) for j, (B, L, c) in enumerate(F) if sm <= c]
        best = max(vals)
        if best[1] != k:
            bad += 1
        E = best[0]
        Lk = F[k][1]
        assert F[k][0] == E + Lk * sm          # B = E - s E'  with E' = -Lam_k
    print(f'Legendre B_k = E(s) - s E\'(s), Lam_k = -E\'(s) on the k-th piece: exact; pieces whose midpoint is won by another face: {bad}')
    # second differences of s_k in Lam (smoothness of the discrete flow)
    d2 = [float(s[k + 1] - 2 * s[k] + s[k - 1]) for k in range(2, len(F) - 1)]
    print(f'second differences of s_k (dLam = 0.005 fixed): min {min(d2):.2e}, max {max(d2):.2e}')
    return steps, F, s


def ode_compare(F, s):
    sys.path.insert(0, os.path.join(HERE, '..', 'newpowers', 'ta'))
    import ode2
    t0 = time.time()
    c = ode2.Chain2(gain=1.0, Lend=1.90)
    print(f'ODE solved in {time.time() - t0:.0f}s, Lmin {c.Lmin:.4f}')
    print('  k    Lam      B_chain      B_ODE(Lam)   B_ODE-B_chain   s0_chain   s0_ODE(B_chain,Lam_chain)')
    for k in [1, 10, 20, 40, 60, 80, 100, 120, 129]:
        B, L, _ = F[k]
        Bo = c.B(float(L))
        so = c.s0(float(B), float(L))
        print(f'  {k:3d}  {float(L):.4f}  {float(B):.9f}  {Bo:.9f}  {Bo - float(B):+.3e}     {float(s[k]):.6f}   {so:.6f}')


if __name__ == '__main__':
    steps, F, s = exact_checks()
    if '--ode' in sys.argv:
        ode_compare(F, s)
