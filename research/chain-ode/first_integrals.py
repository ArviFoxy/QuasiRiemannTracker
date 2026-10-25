"""First integrals of the continuum source-chain flows from their Darboux integrating factors.
late  (gain at cap):      mu = 1/(E^2 (3E-2)),        F = 10 s/E + log(3 - 2/E)
early (class p = 1/2):    mu = 1/(E^2 (11E+9s-9)),    F computed below.
Run: python3 first_integrals.py"""
import sympy as sp, math
s, E = sp.symbols('s E', positive=True)
def first_integral(M, N, mu):
    Fs = sp.simplify(mu*M)
    F0 = sp.integrate(Fs, s)
    phi_p = sp.simplify(mu*N - sp.diff(F0, E))
    assert sp.simplify(sp.diff(phi_p, s)) == 0, phi_p
    F = sp.simplify(F0 + sp.integrate(phi_p, E))
    # check exactness
    assert sp.simplify(sp.diff(F, s) - mu*M) == 0 and sp.simplify(sp.diff(F, E) - mu*N) == 0
    return F
cases = {
 'late':  (E*(15*E-10), E - 15*s*E + 10*s, 1/(E**2*(3*E-2))),
 'early': (5*E*(5*E+4*s-4), (3*E+2*s-2) - 5*s*(5*E+4*s-4), 1/(E**2*(11*E+9*s-9))),
}
Fs = {}
for name, (M, N, mu) in cases.items():
    F = first_integral(M, N, mu)
    Fs[name] = (F, M, N)
    print(name, ': F =', F)
# numerical check: integrate E' = -M/N with RK4 and watch F
for name, (F, M, N) in Fs.items():
    f = sp.lambdify((s, E), -M/N); Fn = sp.lambdify((s, E), F)
    ss, EE, h = 0.0135, 0.94, 1e-6
    vals = [Fn(ss, EE)]
    for k in range(20000):
        k1 = f(ss, EE); k2 = f(ss+h/2, EE+h*k1/2); k3 = f(ss+h/2, EE+h*k2/2); k4 = f(ss+h, EE+h*k3)
        EE += h*(k1+2*k2+2*k3+k4)/6; ss += h
    vals.append(Fn(ss, EE))
    print(f"{name}: F(start) = {vals[0]:.15f}, F(s={ss:.4f}, E={EE:.6f}) = {vals[1]:.15f}")
