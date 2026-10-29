"""Value of the whole window to the current return: count face (B, Lam, cap) with B = 1 (every plain mass the
current machinery admits at s = 0) and the physical capacity saturated at numeratorCap.  Also the exact ODE
shape (today's method in the limit) for reference.  [numerical; hypothetical faces]"""
from globalcheck import theta_global
from levers import curve, d
from levers_global import phys_face
from scipy.optimize import brentq

Bc = curve(2.5715, 0.99999)
Lq = brentq(lambda L: d * L / (6 * Bc(L) - L) - 0.5, 1.75, 2.5)
for name, cf, pf in [('exact ODE (today, limit)', (Bc(Lq), Lq, 0.09999), phys_face(Bc, Lq)),
                     ('zone: count (1, 1.9265, 0.12), phys saturated', (1.0, 1.9265, 0.12), (0.99999, 2.2515)),
                     ('zone: count (1, 1.9265, 0.15), phys saturated', (1.0, 1.9265, 0.15), (0.99999, 2.2515))]:
    t, where = theta_global(cf, pf)
    print('%-48s global theta*=%.8f  %+.2e  binding %s d=%.2f p=%.2f %s' % ((name, t, t - 0.8738723399) + where), flush=True)
