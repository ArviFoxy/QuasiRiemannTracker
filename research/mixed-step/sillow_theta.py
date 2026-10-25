"""theta* if the LOW branch were Sil's argument at native rate q (parentless), HIGH as now.
Faces are tangent lines of the envelope E(s) = max{E : E + Qs(q*)s <= 1}; P = the slope-3 face,
C scanned over s."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'faceless-chain'))
from fractions import Fraction as Fr
from scipy.optimize import brentq
import closed_flow as CF, theta_eval as T
Qs = lambda q: (2 + 6*q)/(1 + q)
qst = lambda s, E: max(CF.q6star(s, E)[0]/6, 0.5)
E = lambda s: brentq(lambda e: e + Qs(qst(s, e))*s - 1, 0.5, 0.99999, xtol=1e-14)
def face(s, h=1e-6):
    L = (E(s - h) - E(s + h))/(2*h)
    return E(s) + L*s, L
CAP = Fr(549989, 10**7)
fr = lambda x: Fr(x).limit_denominator(10**12)
sP = brentq(lambda s: face(s)[1] - 3.0001, 0.03, 0.05)
BP, LP = face(sP)
print(f"P: s={sP:.5f} B={BP:.6f} L={LP:.5f}", flush=True)
for sC in [float(a) for a in sys.argv[1:]]:
    BC, LC = face(sC)
    th = T.theta_star((fr(BC*(1-2e-9)), fr(LC), CAP), (fr(BP*(1-2e-9)), fr(LP), CAP), lo=8700000)
    print(f"C: s={sC:.4f} B={BC:.6f} L={LC:.5f} theta*={th}", flush=True)
