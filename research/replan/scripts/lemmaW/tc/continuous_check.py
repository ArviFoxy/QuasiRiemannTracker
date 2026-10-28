# how conservative is the Bernstein cover? continuous optimum of the C-branch return at the binding edge (float, 1e-12) vs exact cover theta*
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import brentq, minimize_scalar
import pr86, cert_return as CR
cfg0 = pr86.Cfg()          # PR 86 faces and constants, h = 8051/10000
def margin_max(th):
    cfg = cfg0.copy(th=Fr(th).limit_denominator(10**12))
    pr86.apply_globals(cfg)
    G = pr86.geometry(cfg)
    edges = {nm: (d, C) for nm, d, C in pr86.edge_list(cfg, G)}
    d, C = edges['newTop']
    cands = {nm: b for nm, b, meta in pr86.candidate_list(cfg, G)}
    br = cands['C']
    def ev(a, dl, p): return sum(float(c)*dl**i*p**j for (i, j), c in a.items())
    def E(dl, p=0.5):
        J = ev(br['J'], dl, p); N = ev(br['N'], dl, p)
        Eb = float(Fr(1, 2) + 13*G['h']/75 - G['y']/2 - G['ell']/2 - Fr(9, 100)*d) + dl/2 + dl*p*float(G['ell'] - C/2)
        return Eb + 0.75*float(d)*N/J
    r = minimize_scalar(lambda x: -E(x), bounds=(0.40, 0.48), method='bounded', options=dict(xatol=1e-12))
    return -r.fun, r.x
f = lambda th: th - float(cfg0.reserve) - margin_max(th)[0]
th_c = brentq(f, 0.8739, 0.8741, xtol=1e-14)
print('continuous optimum of the C branch at (newTop, p=1/2): theta_c = %.10f at delta* = %.5f' % (th_c, margin_max(th_c)[1]))
print('exact cover theta* (h=0.8051, 1e-9 resolution) = 0.873955786')
