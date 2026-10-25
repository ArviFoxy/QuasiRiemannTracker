"""Where Lambert W comes from.
Class p flow as a polynomial vector field X = (s', E') = (D - 5As, -5AE) (time-rescaled), with
A = (3-p)E + 4ps - 2, D = (1+p)E + 4p^2 s - 2p and the cutoff root xi = E + 2ps:
  A = (1-p)E - 2(1-xi),  D = (1-p)E - 2p(1-xi),  D - pA = (1-p)^2 E.
Hence X(g/E) is CONSTANT for g = 5s - p:  X((5s-p)/E) = 5(1-p)^2.
So the line E = 0 carries the exponential factor exp((5s-p)/E) (a double invariant line), the line
L_p = 0 is invariant with cofactor -5A - 2(5-2p^2), and L_p/E * exp(kappa (5s-p)/E) is a first
integral. In the flow's own time, (5s-p)/E grows linearly while L_p/E decays exponentially:
x e^x = const, i.e. Lambert W.
"""
import sympy as sp
p, s, E = sp.symbols('p s E')
A = (3 - p)*E + 4*p*s - 2
D = (1 + p)*E + 4*p**2*s - 2*p
xi = E + 2*p*s
print('A form:', sp.expand(A - ((1 - p)*E - 2*(1 - xi))))
print('D form:', sp.expand(D - ((1 - p)*E - 2*p*(1 - xi))))
print('D - pA - (1-p)^2 E:', sp.expand(D - p*A - (1 - p)**2*E))
Xs, XE = D - 5*A*s, -5*A*E
X = lambda f: sp.expand(sp.diff(f, s)*Xs + sp.diff(f, E)*XE)
g = 5*s - p
print('X(g/E) =', sp.simplify((X(g)*E - g*X(E))/E**2))
Lp = (3 - 2*p)*(5 + p)*E + 4*p*(5 - 2*p**2)*s - 2*(5 - 2*p**2)
print('cofactor of L_p:', sp.factor(sp.simplify(X(Lp)/Lp)), ' check -5A-2(5-2p^2):',
      sp.simplify(X(Lp)/Lp - (-5*A - 2*(5 - 2*p**2))))
kap = 2*(5 - 2*p**2)/(5*(1 - p)**2)
I = sp.log(Lp/E) + kap*g/E
print('X(I) =', sp.simplify(sp.diff(I, s)*Xs + sp.diff(I, E)*XE))
# extactic polynomial for lines: multiplicity of E = 0
v = [sp.Integer(1), s, E]
row1 = [X(f) for f in v]; row2 = [X(f) for f in row1]
ext = sp.factor(sp.Matrix([v, row1, row2]).det())
print('extactic (lines) =', ext)
