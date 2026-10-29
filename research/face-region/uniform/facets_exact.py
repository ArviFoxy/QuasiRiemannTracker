import sympy as sp
p, w, B, L, S, Q, h0, K = sp.symbols('p w B Lambda S Q h0 K', real=True)
one, half = sp.Integer(1), sp.Rational(1, 2)
def facets(Kval=8):
    nu6 = 5 - w
    base = 10/(10 + w)
    inv = {0: (one, -2*p*Kval*S), 1: (one/(1 - p), -p*Q/(1 - p))}
    pl = {0: (one, -2*p*S), 1: (one, -2*p*h0*Q), 2: (L/(L - 2*p), -2*p*B*Q/(L - 2*p))}
    phi = {}
    for i, (si, oi) in inv.items():
        for j, (sj, oj) in pl.items():
            slope = nu6 + w*(si + sj*half)
            off = w*(oi + oj*half)
            phi[(i, j)] = sp.together((1 - 2*p)*S + (5*Q - off)/slope - base*Q)
    return phi
phi = facets()
if __name__ == '__main__':
    for k in [(1, 0), (1, 1), (1, 2)]:
        f = phi[k]
        diff = sp.factor(sp.together(f - f.subs(p, half)))
        print('phi%s(p) - phi%s(1/2) =' % (k, k), diff)
        print()
