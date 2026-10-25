"""Degrees of the cleared gates along a polynomial secant family (symbolic s, u, p)."""
import sympy as sp, sys, json, numpy as np
from fractions import Fraction as Fr
s, u, p = sp.symbols('s u p')
dE = int(sys.argv[1]) if len(sys.argv) > 1 else 3
rows = json.load(open('cont_lean.json')); rows = [r for r in rows if r['s'] <= 0.04236]
S_ = np.array([r['s'] for r in rows]); E_ = np.array([r['E'] for r in rows])
c = np.polyfit(S_, E_, dE)[::-1]
Et = sum(sp.Rational(Fr(float(ci)).limit_denominator(10**12)) * s**k for k, ci in enumerate(c))
D = sp.Rational(1, 10**9); dl = sp.Rational(426, 10**8); cap = sp.Rational(549989, 10**7)
e, r, f = sp.Rational(1, 10**17), sp.Rational(1, 10**12), sp.Rational(1, 10**10)
Lf = lambda x: sp.expand((Et.subs(s, x) - Et.subs(s, x + D))/D)
Bf = lambda x: sp.expand(Et.subs(s, x) + x*Lf(x))
B, L, B0, L0 = Bf(s), Lf(s), Bf(s - D), Lf(s - D)
q = (1 - dl)*L0/(6*B0)
def gates_at(b):
    t = B - L*(b - e); T = t + b; S = b - 2*e
    a = (q*(b + (t - B0)/L0) + r)/dl; F = 1 - 6*a - e
    nu = q + u*(sp.Rational(3, 4) - q)
    tt = 15 - 6*nu
    base = (a - nu*T)*tt + (10 - 60*a)*nu + tt*(1 - 2*p)*nu*S - 10*nu*F - f*tt
    out = {}
    for i in range(2):
        dI = 1 if i == 0 else 1 - p
        bI = 2*p*8*S if i == 0 else p*F
        for j in range(3):
            eP = 1 if j < 2 else L0 - 2*p
            gP = 1 if j < 2 else L0
            hP = (2*p*S, 2*p*cap*F, 2*p*B0*F)[j]
            M = 12*nu*(dI*eP) + (5 - 6*nu)*(2*eP + dI*gP)
            N = 10*F*(dI*eP) + (5 - 6*nu)*(2*eP*bI + dI*hP)
            out[(i, j)] = M*base + nu*tt*N
    return out
for bname, b in (('cross', s), ('cap', cap)):
    g = gates_at(b)
    for k, v in list(g.items())[:6]:
        num, den = sp.fraction(sp.together(v))
        P = sp.Poly(sp.expand(num), s, u, p)
        print(bname, k, 'deg(s,u,p) =', P.degree(s), P.degree(u), P.degree(p), ' denominator deg_s', sp.Poly(den, s).degree(), flush=True)
