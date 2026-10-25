"""Binding amplitude class p*(s,E) of the switching chain flow: d/dp of 6q_p = 5A/B vanishes,
A = (3-p)E + 4ps - 2, B = (1+p)E + 4p^2 s - 2p. The condition A_p B - A B_p = 0 is quadratic in p.
Run: python3 pstar.py"""
import sympy as sp, numpy as np
s, E, p = sp.symbols('s E p', real=True)
A = (3-p)*E + 4*p*s - 2; B = (1+p)*E + 4*p**2*s - 2*p
cond = sp.expand(sp.diff(A, p)*B - A*sp.diff(B, p))
poly = sp.Poly(cond, p)
print('condition (quadratic in p):', sp.factor(poly.as_expr()))
print('coefficients [p^2, p, 1]:', [sp.factor(c) for c in poly.all_coeffs()])
roots = sp.solve(cond, p)
for r in roots: print('root:', sp.simplify(r))
# check against numeric argmax at the chain points
P = np.linspace(0, 0.5, 200001)
for (sv, Ev) in [(0.03, 0.8734638), (0.0412, 0.8371464), (0.045, 0.8262533)]:
    v = 5*((3-P)*Ev + 4*P*sv - 2)/((1+P)*Ev + 4*P**2*sv - 2*P)
    pn = P[np.argmax(v)]
    rv = [complex(r.subs({s: sv, E: Ev})) for r in roots]
    print(f"s={sv} E={Ev}: numeric p*={pn:.5f}  quadratic roots={[round(x.real,5) for x in rv]}")
