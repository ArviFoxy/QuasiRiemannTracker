"""Closed-form slope law of the mixed flow when HIGH branch 5 at (nu = q, p = 1/2, b = s) binds.

Triple point (REPORT.md section 2): at the crossing b = s with the self HIGH parent (B, L),
  T = t + s = E + s,   the plain threshold P(xi) = (L xi - B)/(L - 1) equals t = E at xi = T,
  so branches 3 and 5 tie and the HIGH gate at p = 1/2 reads (a ~ 0)
      q xi + (kL - q) * ( I(xi) + P(xi)/2 ) <= kL,   xi = T + mh/q,
      I(xi) = (cI xi - 1)/(cI - 1)        (inverse cap z = (1 - r)/cI)
  which gives the HIGH floor q_min(E, s, L).  The mixed LOW step pins q at
      den3 = 1 + q - 6 q B/L = 0   <=>   L = 6 q E/(1 + q - 6 q s).
The flow is E' = -L(E, s).  usage: python3 closed_form.py [kL] [cI] [mh] [dxi]
"""
import sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__))


def lhs(q, xi, E, s, L, kL, cI):
    B = E + L*s
    I = (cI*xi - 1)/(cI - 1)
    P = (L*xi - B)/(L - 1)
    return q*xi + (kL - q)*(I + P/2) - kL


def q_min(E, s, L, kL=5/6, cI=2.0, mh=1e-4, dxi=0.0):
    lo, hi = 0.3, 0.75
    for _ in range(80):
        q = 0.5*(lo + hi)
        xi = E + s + mh/q - dxi          # required root (dxi: a uniform bonus to the root)
        if lhs(q, xi, E, s, L, kL, cI) <= 0: hi = q
        else: lo = q
    return hi


def slope(E, s, kL=5/6, cI=2.0, mh=1e-4, dxi=0.0, L0=2.2, qtop=0.749, qfloor=0.5):
    L = L0
    for _ in range(200):
        q = min(max(q_min(E, s, L, kL, cI, mh, dxi), qfloor), qtop)
        Ln = 6*q*E/(1 + q - 6*q*s)
        if abs(Ln - L) < 1e-13: break
        L = Ln
    return L, q


def flow(kL=5/6, cI=2.0, mh=1e-4, dxi=0.0, s0=0.016, s_end=0.062, ds=5e-4):
    from fractions import Fraction as Fr
    fan = json.load(open(os.path.join(HERE, '..', 'mixed-step', 'fan_16_1000.json')))
    L = float(Fr(fan[-1]['L'])); E = float(Fr(fan[-1]['B'])) - L*s0
    s = s0; rows = []
    while s <= s_end + 1e-12:
        L, q = slope(E, s, kL, cI, mh, dxi, L)
        rows.append(dict(s=s, E=E, L=L, q=q, B=E + L*s))
        Lm, _ = slope(E - L*ds/2, s + ds/2, kL, cI, mh, dxi, L)
        E -= Lm*ds; s = round(s + ds, 12)
    return rows


if __name__ == '__main__':
    kL = float(sys.argv[1]) if len(sys.argv) > 1 else 5/6
    cI = float(sys.argv[2]) if len(sys.argv) > 2 else 2.0
    mh = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-4
    dxi = float(sys.argv[4]) if len(sys.argv) > 4 else 0.0
    rows = flow(kL, cI, mh, dxi)
    for r in rows[::8] + [rows[-1]]:
        print(f"s={r['s']:.4f} E={r['E']:.6f} L={r['L']:.5f} q={r['q']:.4f}")
