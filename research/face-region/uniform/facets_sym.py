"""Symbolic facets of the repeated-mark gain per unit nu:  phi_ij(p) = (1-2p) S + root_ij(p) - base*Q,
root_ij = (5Q - off_ij)/slope_ij, slope = 6nu + w(si + sj/2), off = w(oi + oj/2), 6 nu = 5 - w, base = 10/(10+w)."""
import sympy as sp
p, w, B, L, S, Q, h0, K = sp.symbols('p w B Lambda S Q h0 K', real=True)
nu6 = 5 - w
base = 10/(10 + w)
inv = {0: (1, -2*p*K*S), 1: (1/(1 - p), -p*Q/(1 - p))}
pl = {0: (1, -2*p*S), 1: (1, -2*p*h0*Q), 2: (L/(L - 2*p), -2*p*B*Q/(L - 2*p))}
phi = {}
for i, (si, oi) in inv.items():
    for j, (sj, oj) in pl.items():
        slope = nu6 + w*(si + sj/2)
        off = w*(oi + oj/2)
        root = sp.simplify((5*Q - off)/slope)
        phi[(i, j)] = sp.simplify((1 - 2*p)*S + root - base*Q)
for k, f in phi.items():
    print(k, sp.factor(sp.together(f)))
# at p = 0 all equal S ; at p = 1/2:
for k, f in phi.items():
    print('p=1/2', k, sp.factor(sp.simplify(f.subs(p, sp.Rational(1, 2)))))
import pickle
pickle.dump({str(k): sp.srepr(v) for k, v in phi.items()}, open('phi.pkl', 'wb'))
