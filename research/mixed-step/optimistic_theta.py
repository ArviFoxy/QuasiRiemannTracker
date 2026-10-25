"""Score the optimistic mixed-step readings (erase6: Qeff = 6q/(1+q); erase4: 4q/(1+q)) with the
physical slope receipt `source_lambda_low` (LP > 3) dropped, as Lemma D would allow (hypothetical).
P and C are scanned over the family's faces."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'faceless-chain'))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import qeff_models as M
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
CAP = Fr(549989, 10**7)
fr = lambda x: Fr(x).limit_denominator(10**12)
def ok(th, C, P):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), Fr(401, 500), C, P, verbose=False, sP=Fr(9, 200),
                               sC=Fr(13, 250), mode='global')
        return not bad
    except (ValueError, AssertionError):
        return False
def theta_star(C, P, lo=8740000, hi=8747400):
    if not ok(hi, C, P): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, C, P) else (mid, hi)
    return hi
model = sys.argv[1]
s0, C, P = M.run(model)
import numpy as np
# rebuild the face list
out = []
Qf = M.MODELS[model]
def faces(model):
    import closed_flow as CF
    from scipy.optimize import brentq
    B0, lam = 0.99999, 3.72
    def slope(s, E):
        q = max(CF.q6star(s, E)[0]/6, 0.5); Q = Qf(q)
        return Q*E/((1 - Q*s)*(1 - M.DEN))*(1 + M.PHI)
    s, E = s0, B0 - lam*s0; h = (0.06 - s)/20000; res = []
    for i in range(20000):
        L = slope(s, E); res.append((s, E + L*s, L))
        f = lambda s_, E_: -slope(s_, E_)
        k1 = f(s, E); k2 = f(s + h/2, E + h*k1/2); k3 = f(s + h/2, E + h*k2/2); k4 = f(s + h, E + h*k3)
        E += h*(k1 + 2*k2 + 2*k3 + k4)/6; s += h
    return res
F = faces(model)
pick = lambda s: min(F, key=lambda o: abs(o[0] - s))
for sP in [float(x) for x in sys.argv[2].split(',')]:
    for sC in [float(x) for x in sys.argv[3].split(',')]:
        p, c = pick(sP), pick(sC)
        th = theta_star((fr(c[1]*(1-2e-9)), fr(c[2]), CAP), (fr(p[1]*(1-2e-9)), fr(p[2]), CAP))
        print(f"{model} P s={p[0]:.4f} ({p[1]:.5f},{p[2]:.4f})  C s={c[0]:.4f} ({c[1]:.5f},{c[2]:.4f})  theta*={th}", flush=True)
