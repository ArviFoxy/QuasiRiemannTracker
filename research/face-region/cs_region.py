"""Cauchy-Schwarz (D8a) closure of the proven face region of the density chain.

Coordinates: m1, m2 = plain lengths, s = total slot width, all in units of log Z at M = 1.
Proven face region (130 faces of research/chain/steps_f050_dL200.json):
    R = {(m1, m2, s) : m1, m2 >= 0, 0 <= s <= cap_k, m1 + m2 + Lam_k s <= B_k for some k}.
Its projection to (s, P = m1 + m2) is the hypograph of E(s) = max_k (B_k - Lam_k s).

Cauchy-Schwarz over the row sum z (energy = sum_z w(z)|R1 R2 S_A S_B|^2, w >= 0):
    E(m1, m2, sA + sB) <= E(m1, m1, 2 sA)^(1/2) E(m2, m2, 2 sB)^(1/2).
Hence the closure  R_CS = R  u  {(m1, m2, sA + sB) : (m1, m1, 2sA) in R, (m2, m2, 2sB) in R}.

Facts checked here (exact where stated):
 (a) balanced slice m1 = m2: R_CS = R (no gain at all): the squared configurations of a balanced target are
     (m, m, 2 sA), (m, m, 2 sB), with the same total P = 2m, and max(2sA, 2sB) >= sA + sB (Lean: balanced_no_gain);
 (b) the (s, P) upper boundary of R_CS is the MIDPOINT set P_CS(s) = max_{s'+s''=2s} (E(s') + E(s''))/2,
     not the convex hull (chord): CS gives equal weights only, and further Holder exponents do not help;
 (c) at given P the CS capacity is s_CS(P) = max_a (s*(P + 2a) + s*(P - 2a))/2, attained by the
     plain pair (m1, m2) = ((P + 2a)/2, (P - 2a)/2): an UNBALANCED pair with |m1 - m2| = 2a.
"""
from fractions import Fraction as Fr
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from faces import load_faces, E as Eexact

steps, FACES = load_faces()
FF = [(float(B), float(L), float(c)) for B, L, c in FACES]
CAPMAX = max(c for _, _, c in FF)


def E(s):
    """envelope; -inf if no face admits s"""
    best = float('-inf')
    for B, L, c in FF:
        if 0 <= s <= c + 1e-15:
            best = max(best, B - L * s)
    return best


def sstar(P):
    """face capacity at total plain length P: max s with P <= E(s) (E is decreasing on [0, 0.1];
    beyond 0.1 only face 0 (cap 0.1397) survives).  None if P > E(0)."""
    best = None
    for B, L, c in FF:
        if P <= B:
            s = min(c, (B - P) / L)
            if best is None or s > best:
                best = s
    return best


def P_cs(s, n=4000):
    """max (E(s1) + E(s2))/2 over s1 + s2 = 2 s, s1, s2 in [0, CAPMAX]"""
    best = E(s)
    lo, hi = max(0.0, 2 * s - CAPMAX), min(2 * s, CAPMAX)
    for i in range(n + 1):
        s1 = lo + (hi - lo) * i / n
        s2 = 2 * s - s1
        v = (E(s1) + E(s2)) / 2
        if v > best:
            best = v
    return best


def P_cs_arg(s, n=4000):
    best, arg = E(s), (s, s)
    lo, hi = max(0.0, 2 * s - CAPMAX), min(2 * s, CAPMAX)
    for i in range(n + 1):
        s1 = lo + (hi - lo) * i / n
        s2 = 2 * s - s1
        v = (E(s1) + E(s2)) / 2
        if v > best:
            best, arg = v, (s1, s2)
    return best, arg


def s_cs(P, n=4000):
    """CS capacity at total P, and the optimal plain pair (m1, m2)"""
    best, pair = sstar(P), (P / 2, P / 2)
    if best is None:
        best = float('-inf')
    E0 = E(0.0)
    amax = (E0 - P) / 2          # need 2 m1 = P + 2a <= E(0)
    if amax < 0:
        return best, pair
    for i in range(n + 1):
        a = amax * i / n
        s1, s2 = sstar(P + 2 * a), sstar(P - 2 * a)
        if s1 is None or s2 is None:
            continue
        v = (s1 + s2) / 2
        if v > best + 1e-15:
            best, pair = v, ((P + 2 * a) / 2, (P - 2 * a) / 2)
    return best, pair


def chord(s):
    return E(0.0) + (E(0.1) - E(0.0)) * s / 0.1


if __name__ == '__main__':
    print('E(0) = %.6f, E(0.1) = %.6f, chord slope = %.6f' % (E(0), E(0.1), (E(0.1) - E(0)) / 0.1))
    print('\n(b) upper boundary in the (s, P) plane: envelope E, CS midpoint set P_CS, chord (claimed hull)')
    print('   s      E(s)      P_CS(s)   gain_CS   chord     gain_chord(claimed)  optimal (s1, s2)')
    for s in [0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.09, 0.1]:
        v, (s1, s2) = P_cs_arg(s)
        print(f'  {s:.2f}  {E(s):.6f}  {v:.6f}  {v - E(s):+.6f}  {chord(s):.6f}  {chord(s) - E(s):+.6f}            ({s1:.4f}, {s2:.4f})')
    print('\n(c) CS capacity at given total P (the plain pair realising it is unbalanced)')
    print('   P        s*(P)     s_CS(P)   gain      pair (m1, m2)')
    for P in [0.95, 0.92, 0.90, 0.88, 0.8512, 0.85, 0.83, 0.80, 0.78, 0.77]:
        b = sstar(P)
        v, (m1, m2) = s_cs(P)
        print(f'  {P:.4f}  {b:.6f}  {v:.6f}  {v - b:+.6f}  ({m1:.5f}, {m2:.5f})')
