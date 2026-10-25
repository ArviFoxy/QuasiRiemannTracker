"""AM-GM form of the binding threshold.
Class p: 6q_p = 5A/D, A = (3-p)E + 4ps - 2, D = (1+p)E + 4p^2 s - 2p.
(1) mixture identity D = p A + (1-p)^2 E.
(2) SOS identity (E = a^2, s = b^2):
    (a+2b)^2 [ (a-2b)^2 D - (2 - a^2 - 4ab) A ] = 4 (b A - a(1 - a^2 - 2b^2))^2,
so 6q_p <= 5(a-2b)^2/(2 - a^2 - 4ab) for every class p (D > 0, 2 - a^2 - 4ab > 0), with equality iff
b A_p = a(1 - a^2 - 2b^2): the binding class.
"""
import sympy as sp
p, a, b = sp.symbols('p a b', real=True)
E, s = a**2, b**2
A = (3 - p)*E + 4*p*s - 2
D = (1 + p)*E + 4*p**2*s - 2*p
print('mixture:', sp.expand(D - (p*A + (1 - p)**2*E)))
lhs = (a + 2*b)**2*((a - 2*b)**2*D - (2 - a**2 - 4*a*b)*A)
rhs = 4*(b*A - a*(1 - a**2 - 2*b**2))**2
print('SOS identity:', sp.expand(lhs - rhs))
pstar = sp.solve(sp.Eq(b*A, a*(1 - a**2 - 2*b**2)), p)
print('equality class p* =', [sp.factor(x) for x in pstar])
