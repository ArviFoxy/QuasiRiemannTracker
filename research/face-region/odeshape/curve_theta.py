"""theta* of the return when its two faces are read off the explicit curve (curve_6.json): count face = the
curve's end (L_a, beta(L_a)) with cap 9999/100000; physical face = the curve point maximising the newTop capacity."""
import sys, os, json
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import minimize_scalar
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shape'))
from theta_of_faces import theta_star
c = json.load(open(sys.argv[1] if len(sys.argv) > 1 else 'curve_6.json'))
La, Lb, Lm = Fr(c['La']), Fr(c['Lb']), Fr(c['Lm']); Lh = (Lb - La)/2
coef = [Fr(x) for x in c['coef_t']]
beta = lambda L: sum(float(k)*((L - float(Lm))/float(Lh))**i for i, k in enumerate(coef))
y2, dp = 2*69313573/150000000, 0.8044451001
cap = lambda L: (y2 - (2 - beta(L))*dp)/L
Lp = minimize_scalar(lambda L: -cap(L), bounds=(2.1, 2.4), method='bounded', options={'xatol': 1e-10}).x
cB, cL = Fr(beta(float(La))).limit_denominator(10**12), La
pB, pL = Fr(beta(Lp)).limit_denominator(10**12), Fr(Lp).limit_denominator(10**12)
t, d0, gw, cp = theta_star(cB, cL, pB=pB, pL=pL)
print('count face (L=%.8f, B=%.8f); physical face (L=%.6f, B=%.8f, capacity %.8f)' % (float(cL), float(cB), Lp, float(pB), cp))
print('theta* = %.10f   vs merged 0.87387234: %+.2e' % (float(t), float(t) - 0.87387234))
