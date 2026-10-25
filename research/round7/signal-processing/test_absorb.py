# Check: g~(n) * conj((n/P)_3) == g~(nP)/g~(P)  (slot twist chi_P(n)^{-2} = conj((n/P)_3) with sextic chi)
import sys; sys.path.insert(0, '.')
from zw import *
ar = Arith(30000)
primes = ar.elems(1, 30000, primes_only=True)
gtab = GaussTable(ar, primes)
cols = [c for c in ar.elems(100, 300)]
marks = [P for P in ar.elems(60, 100, primes_only=True)]
mx_abs, mx_non = 0, 0
for n in cols:
    for P in marks:
        if P['ps'][0] in n['ps']: continue
        # product element nP: multiply a+b w
        a1,b1,a2,b2 = n['a'],n['b'],P['a'],P['b']
        a, b = a1*a2 - b1*b2, a1*b2 + a2*b1 - b1*b2     # (a1+b1w)(a2+b2w), w^2 = -1-w
        m = dict(a=a, b=b, N=n['N']*P['N'], ps=n['ps']+P['ps'], rs=n['rs']+P['rs'])
        lhs_abs = gtab.gt(n) * np.conj(cubic_sym_elem(ar, a1, b1, P['ps'][0], P['rs'][0]))
        lhs_non = gtab.gt(n) * cubic_sym_elem(ar, a1, b1, P['ps'][0], P['rs'][0])
        rhs = gtab.gt(m) / gtab.gt(P)
        mx_abs = max(mx_abs, abs(lhs_abs - rhs)); mx_non = max(mx_non, abs(lhs_non - rhs))
print("max |g~(n)conj((n/P)_3) - g~(nP)/g~(P)| =", mx_abs, "  (other orientation:", mx_non, ")")
