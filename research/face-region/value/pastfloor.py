"""The density curve continued past q = 1/2 (same kappa(q)): best count face over L in [1.80, 1.93], global check."""
from levers import curve
from levers_global import phys_face
from globalcheck import theta_global
Bc = curve(2.5715, 0.99999)
PF = phys_face(Bc, 1.93)
best = None
for L in (1.80, 1.84, 1.87, 1.90, 1.92, 1.926):
    t, where = theta_global((Bc(L), L, 0.09999), PF)
    print('L=%.3f B=%.6f  global theta*=%.8f  %+.2e  %s' % ((L, Bc(L), t, t - 0.8738723399) + (where,)), flush=True)
