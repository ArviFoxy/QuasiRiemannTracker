"""Envelope if the LOW branch were Sil's direct argument with native rate q (no parent):
E(s) = max{E : E + Qs(q*(s,E))·s <= 1}, Qs(q) = (2+6q)/(1+q), q = max(q*, 1/2).
Compared with the current family's envelope (pure flow from Sil's tangency)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'faceless-chain'))
import numpy as np
from scipy.optimize import brentq
import closed_flow as CF
Qs = lambda q: (2 + 6*q)/(1 + q)
def qstar(s, E): return max(CF.q6star(s, E)[0]/6, 0.5)
def E_sillow(s):
    f = lambda E: E + Qs(qstar(s, E))*s - 1
    return brentq(f, 0.5, 0.99999)
# current family envelope: pure flow from Sil's tangency
import qeff_models as M
s0, C, P = M.run('pure')
print("pure family: C", C[:3], "P", P[:3])
for s in (0.02, 0.03, 0.035, 0.04, 0.045, 0.047):
    E = E_sillow(s)
    print(f"s={s:.3f} sillow E={E:.5f} q*={qstar(s,E):.4f} Qs={Qs(qstar(s,E)):.4f}")
