"""The p-family of continuum chain flows: for binding amplitude class p (inverse-budget and
slot-supply facets), the HIGH gate gives 6q = 5((3-p)E + 4ps - 2)/((1+p)E + 4p^2 s - 2p), and the
chain obeys E' = -6qE/(1 - 6qs). Check: Darboux invariant lines and integrating factor for all p.
Run: python3 family_p.py"""
import sympy as sp
s, E, p = sp.symbols('s E p', positive=True)
num = (3-p)*E + 4*p*s - 2
den = (1+p)*E + 4*p**2*s - 2*p
M = sp.expand(5*E*num)              # E' = -M/N
N = sp.expand(den - 5*s*num)
# invariant lines: try l = E + b s + c with cofactor K: X(l) = K l, X = N d/ds - M d/dE
b, c, k0, k1, k2 = sp.symbols('b c k0 k1 k2')
l = E + b*s + c
K = k0 + k1*s + k2*E
eqs = sp.Poly(sp.expand(N*sp.diff(l, s) - M*sp.diff(l, E) - K*l), s, E).coeffs()
sols = sp.solve(eqs, [b, c, k0, k1, k2], dict=True)
for so in sols:
    print('invariant line:', sp.factor(l.subs(so)), '  cofactor:', sp.factor(K.subs(so)))
# integrating factor E^a * line^m with divergence condition
div = sp.expand(sp.diff(N, s) - sp.diff(M, E))
KE = sp.factor(sp.simplify(N*sp.diff(E, s) - M*sp.diff(E, E)) / E)   # cofactor of E
print('cofactor of E:', KE)
for so in sols:
    line = l.subs(so); Kl = K.subs(so)
    a_, m_ = sp.symbols('a_ m_')
    cond = sp.Poly(sp.expand(a_*KE + m_*Kl + div), s, E).coeffs()
    sol2 = sp.solve(cond, [a_, m_], dict=True)
    print('integrating factor exponents for line', sp.factor(line), ':', sol2)
# verify the integrating factor exactness for general p
for so in sols:
    line = sp.factor(l.subs(so))
    mu = 1/(E**2*line)
    exact = sp.simplify(sp.diff(mu*M, E) - sp.diff(mu*N, s))   # M ds + N dE: d(muM)/dE = d(muN)/ds
    print('exactness residual with mu = 1/(E^2 * line):', exact)

# explicit first integral F_p
line = (2*p-3)*(p+5)*E + 4*p*(2*p**2-5)*s + 2*(5-2*p**2)
mu = 1/(E**2*line)
Fs_ = sp.simplify(mu*M)
F0 = sp.integrate(sp.apart(sp.together(Fs_), s), s)
phi_p = sp.simplify(mu*N - sp.diff(F0, E))
print('phi_p depends on s?', sp.simplify(sp.diff(phi_p, s)) != 0)
Fp = sp.simplify(F0 + sp.integrate(sp.apart(sp.together(phi_p), E), E))
print('F_p =', Fp)
print('exact?', sp.simplify(sp.diff(Fp, s) - mu*M) == 0, sp.simplify(sp.diff(Fp, E) - mu*N) == 0)
for pv in (0, sp.Rational(1, 4), sp.Rational(1, 2)):
    print('p =', pv, ': F =', sp.simplify(Fp.subs(p, pv)))
