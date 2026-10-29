import sympy as sp
from facets_exact import phi, p, w, B, L, S, Q, h0, K, half
# (1,2): phi - phi(1/2) = (1-2p) * N12 / (D1*D2),  D1 > 0, D2 < 0  => need N12 <= 0
f = phi[(1, 2)]
num, den = sp.fraction(sp.factor(sp.together(f - f.subs(p, half))))
print('den =', den)
N12 = sp.expand(sp.cancel(num / (-(2*p - 1))))
print('N12 coefficients in p:')
for k, c in enumerate(reversed(sp.Poly(N12, p).all_coeffs())):
    print('  p^%d:' % k, sp.factor(c))
# (0,j): phi(p) - phi(0) = p * M_j(p); phi(0) = S
for j in range(3):
    g = phi[(0, j)]
    d = sp.factor(sp.together(g - S))
    print('(0,%d): phi - S =' % j, d)
