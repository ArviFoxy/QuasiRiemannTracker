"""The closed-form switching flow (Lambert stage p = 1/2, then the interior class p*), with the
LOW denominator correction: L = 6 q* E/((1 - 6 q* s)(1 - den)). Integrates E(s) by RK4 on a fine grid.
This is the smooth target for the polynomial face family."""
import numpy as np, json, sys

def q6star(s, E):
    ps = (s*(3*E - 2) - np.sqrt(E*s)*(1 - E - 2*s))/(s*(E - 4*s))
    q6p = lambda p: 5*((3 - p)*E + 4*p*s - 2)/((1 + p)*E + 4*p*p*s - 2*p)
    if ps >= 0.5: return q6p(0.5), 0.5
    if ps <= 0.0: return q6p(0.0), 0.0
    a, b = np.sqrt(E), np.sqrt(s)
    return 5*(a - 2*b)**2/(2 - E - 4*a*b), ps

def slope(s, E, den, fudge):
    Q, _ = q6star(s, E)
    return Q*E/((1 - Q*s)*(1 - den))*(1 + fudge)

def flow(s0, E0, s1, n, den=4.26e-6, fudge=0.0):
    ss = np.linspace(s0, s1, n + 1); h = ss[1] - ss[0]
    Es = [E0]; E = E0
    for s in ss[:-1]:
        k1 = -slope(s, E, den, fudge); k2 = -slope(s + h/2, E + h*k1/2, den, fudge)
        k3 = -slope(s + h/2, E + h*k2/2, den, fudge); k4 = -slope(s + h, E + h*k3, den, fudge)
        E += h*(k1 + 2*k2 + 2*k3 + k4)/6; Es.append(E)
    return ss, np.array(Es)

if __name__ == "__main__":
    rows = json.load(open('cont_lean.json'))
    s0, E0 = rows[0]['s'], rows[0]['E']
    ss, Es = flow(s0, E0, 0.04254, 30000)
    for r in rows[::15]:
        i = np.argmin(abs(ss - r['s']))
        print(f"s={r['s']:.5f} E_lean={r['E']:.9f} E_closed={Es[i]:.9f} diff={r['E']-Es[i]:+.2e}")
