"""Why the binding threshold has the form 6q* = 5(sqrt E - 2 sqrt s)^2/(2 - E - 4 sqrt(Es)).

The class thresholds R_p(Q, s, E) = Q*B_p - 5*A_p = 0 (Q = 6q) are quadratic in p. The binding
threshold is their envelope in p, i.e. the p-discriminant of R_p. We show the discriminant is a
norm form X^2 - 16 E s Y^2 with X, Y affine in Q, so it factors over Q(sqrt(Es)).
"""
import sympy as sp
p, s, E, Q, a, b = sp.symbols('p s E Q a b', positive=True)
A = (3 - p)*E + 4*p*s - 2
B = (1 + p)*E + 4*p**2*s - 2*p
R = sp.expand(Q*B - 5*A)
c2, c1, c0 = [sp.expand(R.coeff(p, k)) for k in (2, 1, 0)]
print('R_p = (%s) p^2 + (%s) p + (%s)' % (c2, c1, c0))
disc = sp.expand(c1**2 - 4*c2*c0)
X = Q*(2 - E) - 5*(E + 4*s)
Y = Q - 5
print('disc - (X^2 - 16 E s Y^2) =', sp.simplify(disc - sp.expand(X**2 - 16*E*s*Y**2)))
fac = sp.factor(disc.subs({E: a**2, s: b**2}))
print('disc(E=a^2, s=b^2) =', fac)
roots = sp.solve(sp.Eq(disc.subs({E: a**2, s: b**2}), 0), Q)
print('Q roots:', [sp.factor(r) for r in roots])
# the double root in p at the envelope
for r in roots:
    pr = sp.simplify(-c1/(2*c2)).subs({E: a**2, s: b**2, Q: r})
    print('  p* =', sp.factor(sp.simplify(pr)))
