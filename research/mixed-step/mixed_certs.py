"""Exact (Fraction) mirror of the draft mixed-step gates SourceValid3 (MIXED_STEP_LEMMA.md §3).

Patches `../repeated-marks/lean_certs.py` so that its `check_node` checks:
  den3 = 1 + q - 6 q B0/L0,  X0 = b + (t - B0)/L0,  a = r (pool kept),
  d = (q X0 + 6 q (B0/L0) r)/den3,  F' = 1 - 6a - 6d,
  the 16 scalar gates with den -> den3, F -> F', every pool charge k a -> k (a + d),
  1/75 - a -> 1/75 - a - d, plus the new gates b - 2e - d >= 0 and d >= 0;
  weakCap at F'; densityGate and the HIGH gate with a -> a + d, F -> F' - e, S = b - 2e - d.
"""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import lean_certs as LC

KN = LC.KN

def den3(n, low): return 1 + n['q'] - 6*n['q']*low['B']/low['L']
def X0(n, low, b): return b + (LC.sourceT(n, b) - low['B'])/low['L']
def dsel(n, low, b):
    return (n['q']*X0(n, low, b) + 6*n['q']*low['B']/low['L']*n['lowFee'])/den3(n, low)
def Fmix(n, low, b): return 1 - 6*n['lowFee'] - 6*dsel(n, low, b)
def Atot(n, low, b): return n['lowFee'] + dsel(n, low, b)

def scalarGate(n, low, b):
    a = n['lowFee']; d = dsel(n, low, b); A = a + d
    t = LC.sourceT(n, b); T = t + b; F = Fmix(n, low, b); e = n['allowance']
    Lref = Fr(49, 100) - KN*b
    return [den3(n, low), b - 2*e, a, Fr(1, 75) - A, F - T/2 - 4*e,
            low['B']*F - t - b - 4*e, 1 - n['q']*low['cap'],
            n['lowFee'] - (n['q']*low['B']/low['L'] + n['q']*low['cap'] + 4)*e - 10*e,
            a - 20*e, Lref, 1 - Lref - Fr(1, 2) - KN*b - 10*e,
            Fr(5, 6) + Fr(499, 1000)*Lref - T - 9*A - n['highFee'],
            1 - T - 5*A - n['highFee'], 1 - Fr(1, 50) - T - 4*A - n['highFee'],
            1 - Fr(1, 50) - T - Fr(9, 2)*A - n['highFee'], Lref - 7*A - n['highFee'],
            b - 2*e - d, d + Fr(1, 10**30)]

def weakCap(n, low, b):
    F = Fmix(n, low, b)
    return low['cap']*F - (low['B']*F - LC.sourceT(n, b))/low['L']

def densityGate2(n, low, high, b, nu, j):
    a = Atot(n, low, b); T = LC.sourceT(n, b) + b; S = b - 2*n['allowance'] - dsel(n, low, b)
    F = Fmix(n, low, b) - n['allowance']; fee = n['highFee']
    t = 15 - 6*nu
    H = (a - nu*T)*t + (10 - 60*a)*nu
    fixed = H + (nu*F/2 - (1 - nu)*b - fee)*t
    core = H + (Fr(5, 6)*F - (1 - nu)*b - fee)*t - 10*nu*F
    tiny = H + (nu*(F - Fr(1, 50))/2 - (1 - nu)*b - fee)*t - 10*nu*Fr(1, 50)
    assert high is not None
    return [1, 1, 1, 1, 1, 1, fixed, core, tiny][j]

def highGate(n, low, h, copies, b, nu, p, k):
    d = dsel(n, low, b)
    return LC.gateG(Atot(n, low, b), LC.sourceT(n, b) + b, b - 2*n['allowance'] - d,
                    Fmix(n, low, b) - n['allowance'], n['highFee'], copies,
                    h['B'], h['L'], h['cap'], nu, p, k)

LC.scalarGate = scalarGate
LC.weakCap = weakCap
LC.densityGate2 = densityGate2
LC.highGate = highGate
check_node = LC.check_node
crossing = LC.crossing

FEES = dict(allowance=Fr(1, 10**17), lowFee=Fr(1, 10**12), highFee=Fr(1, 10**10))
def face(B, L, cap, q=Fr(0)):
    return dict(B=Fr(B), L=Fr(L), cap=Fr(cap), q=Fr(q), **FEES)

def cell_ok(n, low):
    """CellRatio at both endpoints: 2(b - 2e) <= F' - e."""
    return all(2*(b - 2*n['allowance']) <= Fmix(n, low, b) - n['allowance']
               for b in (crossing(n, low), n['cap']))
