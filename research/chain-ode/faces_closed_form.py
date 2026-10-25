"""The faces of the source chain as one explicit curve (2026-10-25).

1. Each class flow E' = -6q_p E/(1 - 6q_p s) is solved by the Lambert W function: on a level set of the
   first integral I_p (family_p.py), y = 1/E satisfies (alpha + beta(s) y) exp(gamma(s) y) = C, so
       1/E(s) = W(C gamma/beta * exp(alpha gamma/beta)) / gamma - alpha/beta,
   alpha = (3-2p)(5+p), beta(s) = 4p(5-2p^2)s - 2(5-2p^2), gamma(s) = kappa(5s - p),
   kappa = 2(5-2p^2)/(5(1-p)^2).
2. The binding class p* (pstar.py) gives, wherever 0 < p* < 1/2, the closed form
       6q* = max_p 6q_p = 5(sqrt E - 2 sqrt s)^2 / (2 - E - 4 sqrt(E s)).
   With a = sqrt E, b = sqrt s: 2 - E - 8p*s = (a+2b)^2 (2 - a^2 - 4ab)/(E - 4s) (sympy below).
3. The switching flow with this q* (p* clipped to [0, 1/2], slope capped by the natural face K)
   reproduces envelope_flow.py, i.e. the continuum ceiling.
4. Importance profile: the effect on E(0.0412) and E(0.045) of a better HIGH count (rho lowered by
   eps_H) on a window of slot widths, i.e. where along the chain a new HIGH-count lemma pays.
Run: python3 faces_closed_form.py   (about a minute)
"""
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp
from scipy.special import lambertw
from scipy.optimize import brentq

K_NAT = 4.4973108

# ---------- 1. Lambert W solution of each class flow ----------
def q6(p, s, E):
    return 5*((3-p)*E + 4*p*s - 2)/((1+p)*E + 4*p*p*s - 2*p)

def consts(p, s):
    a = (3-2*p)*(5+p); b = 4*p*(5-2*p*p)*s - 2*(5-2*p*p)
    k = 2*(5-2*p*p)/(5*(1-p)**2); return a, b, k*(5*s - p)

def level(p, s, E):
    a, b, g = consts(p, s); y = 1/E; return (a + b*y)*np.exp(g*y)

def E_lambert(p, s, C, Eguess):
    a, b, g = consts(p, s)
    vals = [1/(lambertw(C*g/b*np.exp(g*a/b), br)/g - a/b) for br in (0, -1)]
    return min(vals, key=lambda z: abs(z - Eguess)).real

print("1. Lambert W solution of the class flows (start s=0.02, E=0.87):")
for p in (0.0, 0.15, 0.22, 0.35, 0.5):
    sol = solve_ivp(lambda s, Y: [-q6(p, s, Y[0])*Y[0]/(1 - q6(p, s, Y[0])*s)], (0.02, 0.05), [0.87],
                    rtol=1e-12, atol=1e-14, dense_output=True)
    C = level(p, 0.02, 0.87)
    err = max(abs(E_lambert(p, s, C, sol.sol(s)[0]) - sol.sol(s)[0]) for s in np.linspace(0.021, 0.05, 15))
    print(f"   p={p:4.2f}: max |E_W - E_ode| = {err:.1e}")

# ---------- 2. closed form of the binding threshold ----------
a, b, P = sp.symbols('a b p', positive=True)
E_, s_ = a**2, b**2
pst = (s_*(3*E_-2) - a*b*(1-E_-2*s_))/(s_*(E_-4*s_))
num = sp.factor(sp.together((2 - E_ - 8*pst*s_)*(E_ - 4*s_)))
print("2. (2 - E - 8 p* s)(E - 4s) =", num)
q6star = sp.simplify(5*(E_-4*s_)/(2 - E_ - 8*pst*s_))
print("   6q* =", sp.factor(q6star))
def q6star_num(s, E):
    ps = (s*(3*E-2) - np.sqrt(E*s)*(1-E-2*s))/(s*(E-4*s))
    if ps >= 0.5: return q6(0.5, s, E), 0.5
    if ps <= 0.0: return q6(0.0, s, E), 0.0
    ra, rb = np.sqrt(E), np.sqrt(s)
    return 5*(ra-2*rb)**2/(2-E-4*ra*rb), ps

# ---------- 3. the switching flow from the closed form ----------
def flow(eps=lambda s: 0.0, s_end=0.0455, ds=2e-6):
    s, E, out = 0.0, 1.0, {}
    marks = (0.0135, 0.02, 0.03, 0.0412, 0.045)
    while s < s_end:
        e = eps(s)
        if e == 0.0:
            Q, ps = q6star_num(s, E) if s > 0 else (1e9, 0.5)
        else:
            Q, ps = q6_eps(s, E, e)
        slope = min(Q*E/(1 - Q*s), K_NAT) if Q*s < 1 else K_NAT
        for m in marks:
            if m not in out and s >= m: out[m] = (E, ps)
        E -= slope*ds; s += ds
    return out

# full HIGH gate with an improved count rho -> rho - eps_H: q(xi_p(q) - E - 2ps) + eps_H = 0
def xi_p(p, q, s):
    k = 5/6 - q
    return (5/6 + k*p*(1/(1-p) + s))/(5/6 + k*(1/(1-p) - 1/2))
def q6_eps(s, E, e):
    # the binding root is the one just below the unperturbed threshold q0 = q6(p)/6
    best = (-1, 0)
    for p in np.linspace(0, 0.5, 51):
        q0 = q6(p, s, E)/6
        if q0 <= 0: continue
        f = lambda q: q*(xi_p(p, q, s) - E - 2*p*s) + e
        lo = 0.5*q0
        if f(lo) >= 0 or f(q0) <= 0: continue
        q = brentq(f, lo, q0)
        if 6*q > best[0]: best = (6*q, p)
    return best

base = flow()
print("3. switching flow with the closed-form q*:")
for m, (E, ps) in sorted(base.items()):
    print(f"   s={m:.4f}  E={E:.7f}  p*={ps:.3f}")
print("   reference (envelope_flow.py / ceiling): E(0.0412)=0.8371464, E(0.045)=0.8262533")

# ---------- 4. importance profile of a HIGH-count improvement ----------
print("4. dE at s=0.0412 / 0.045 from eps_H = 1e-3 on a window [w, w+0.005):")
for w in (0.0, 0.005, 0.01, 0.015, 0.02, 0.025, 0.03, 0.035, 0.04):
    pert = flow(eps=lambda s, w=w: 1e-3 if w <= s < w + 0.005 else 0.0)
    d1 = pert[0.0412][0] - base[0.0412][0]; d2 = pert[0.045][0] - base[0.045][0]
    print(f"   window [{w:.3f},{w+0.005:.3f}): dE(0.0412)={d1:+.2e}  dE(0.045)={d2:+.2e}")
