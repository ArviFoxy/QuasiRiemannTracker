"""Early regime of the switching flow: when does the boundary class p = 1/2 bind?
Q_p = 5A_p/D_p. Q_{1/2} >= Q_p  <=>  A_{1/2} D_p - A_p D_{1/2} >= 0 (positive denominators)."""
import sympy as sp
p, s, E, a, b = sp.symbols('p s E a b', real=True)
A = lambda p: (3 - p)*E + 4*p*s - 2
D = lambda p: (1 + p)*E + 4*p**2*s - 2*p
X = sp.expand(A(sp.Rational(1, 2))*D(p) - A(p)*D(sp.Rational(1, 2)))
h = sp.factor(sp.simplify(X/(sp.Rational(1, 2) - p)))
print('A_half D_p - A_p D_half = (1/2 - p) *', h)
print('check:', sp.expand(X - (sp.Rational(1, 2) - p)*h))
hl = sp.Poly(sp.expand(h), p)
print('h linear in p:', hl.all_coeffs())
# h(0) and h(1/2) (linear: nonneg on [0,1/2] iff both endpoints nonneg)
h0 = sp.factor(sp.expand(h.subs(p, 0))); hh = sp.factor(sp.expand(h.subs(p, sp.Rational(1, 2))))
print('h(0) =', h0); print('h(1/2) =', hh)
# relation to p* >= 1/2: derivative of Q at p = 1/2 has the sign of h(1/2)
num = sp.expand(sp.diff(A(p), p)*D(p) - A(p)*sp.diff(D(p), p))
print('dQ/dp numerator at 1/2:', sp.factor(num.subs(p, sp.Rational(1, 2))))
import numpy as np
for (sv, Ev) in [(0.0123, 0.9445), (0.0161, 0.9279), (0.0194, 0.9142), (0.0199, 0.9121)]:
    print(sv, Ev, 'h(0)=%.5f h(1/2)=%.5f' % (float(h0.subs({s: sv, E: Ev})), float(hh.subs({s: sv, E: Ev}))))
