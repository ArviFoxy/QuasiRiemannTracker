"""Darboux (invariant algebraic curve) search for the continuum source-chain flows.
Polynomial vector field X = N d/ds - M d/dE from E' = -M/N. A Darboux polynomial f satisfies
X(f) = K f with cofactor K of degree <= deg(field) - 1. Run: python3 darboux.py"""
import itertools, sympy as sp
s, E = sp.symbols('s E')

def darboux(M, N, deg):
    mons = [s**i*E**j for i in range(deg+1) for j in range(deg+1-i)]
    cs = sp.symbols(f'c0:{len(mons)}')
    f = sum(c*m for c, m in zip(cs, mons))
    k0, k1, k2 = sp.symbols('k0 k1 k2')
    K = k0 + k1*s + k2*E
    expr = sp.expand(N*sp.diff(f, s) - M*sp.diff(f, E) - K*f)
    eqs = sp.Poly(expr, s, E).coeffs()
    sols = sp.solve(eqs, list(cs) + [k0, k1, k2], dict=True)
    out = []
    for sol in sols:
        ff = sp.factor(f.subs(sol))
        if ff != 0 and sp.Poly(ff, s, E).total_degree() >= 1:
            out.append((ff, sp.factor(K.subs(sol))))
    return out

fields = {
  'late (g=1)':     (sp.expand(E*(15*E-10)), sp.expand(E - 15*s*E + 10*s)),
  'early (p=1/2)':  (sp.expand(5*E*(5*E+4*s-4)), sp.expand((3*E+2*s-2) - 5*s*(5*E+4*s-4))),
}
for name, (M, N) in fields.items():
    print('==', name, ' E\' = -M/N with M =', M, ', N =', N)
    for d in (1, 2):
        res = darboux(M, N, d)
        print(f'  degree {d}:', res if res else 'none')
