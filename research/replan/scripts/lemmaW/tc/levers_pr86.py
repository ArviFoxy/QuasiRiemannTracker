"""Hypothetical return-side levers priced exactly on the PR 86 return (pr86.py):
  dE : additive change of the return exponent E (Ebase constant)          -> theta* shift per unit
  dR : count improvement R_b -> R_b - dR on every non-old branch (N -> N - dR J) in the rows
  dC : capacity improvement C_new -> C_new + dC at the new edges
  Cfull: the numerator's selected slots save delta p C instead of delta p C/2
These are NOT provable today (new analytic input); they only size the missing distance."""
from fractions import Fraction as Fr
import cert_return as CR
import pr86

LEV = {}
_rp0 = CR.return_poly
def return_poly(br, G, d, C):
    dE = Fr(LEV.get('dE', 0)); dR = Fr(LEV.get('dR', 0)); Cfull = LEV.get('Cfull', 0)
    half = Fr(1) if Cfull else Fr(1, 2)
    Eb = CR.add(CR.const(Fr(1, 2) + 13*G['h']/75 - G['y']/2 - G['ell']/2 - Fr(9, 100)*d + dE),
                CR.smul(Fr(1, 2), CR.DEL), CR.smul(G['ell'] - half*C, CR.mul(CR.DEL, CR.PP)))
    thr = G['theta'] - CR.R0
    if dR and 'D' in br:    # non-old branch
        thr_poly = CR.add(CR.const(thr - Eb[(0, 0)]) if False else CR.const(thr), CR.smul(-1, Eb))
        thr_poly = CR.add(thr_poly, CR.const(Fr(3, 4)*d*dR))
        return CR.sub(CR.mul(br['J'], thr_poly), CR.smul(Fr(3, 4)*d, br['N']))
    return CR.sub(CR.mul(br['J'], CR.sub(CR.const(thr), Eb)), CR.smul(Fr(3, 4)*d, br['N']))
CR.return_poly = return_poly

_edge0 = pr86.edge_list
def edge_list(cfg, G):
    E = _edge0(cfg, G)
    dC = Fr(LEV.get('dC', 0))
    return [(nm, d, C + dC if nm.startswith('new') else C) for nm, d, C in E]
pr86.edge_list = edge_list

def set_lev(**kw):
    LEV.clear(); LEV.update(kw)

# ---------- count-formula levers (as research/return-transfer/levers.py): long-line slope kL, inverse slot cost c_I, class 4th-moment saving eta4
const, sub, add, mul, smul, DEL, PP = CR.const, CR.sub, CR.add, CR.mul, CR.smul, CR.DEL, CR.PP
def _branch(A, Z):
    KL = Fr(LEV.get('KL', Fr(5, 6))); CI = Fr(LEV.get('CI', 2))
    Vp = sub(const(KL), DEL)
    pp = smul(2/CI, PP)
    D = add(A, sub(const(1), pp))
    C0 = sub(const(1), Z)
    U = mul(sub(const(1), pp), C0)
    J = add(mul(Vp, D), mul(mul(DEL, sub(const(1), pp)), A))
    N = add(mul(sub(const(1), DEL), J), mul(mul(Vp, DEL), U))
    T = add(J, mul(DEL, U))
    Rn = mul(D, sub(J, mul(Vp, C0)))
    Mn = sub(mul(D, T), Rn)
    return dict(D=D, A=A, C0=C0, U=U, J=J, N=N, T=T, Rn=Rn, Mn=Mn)
_aff0, _old0 = CR.branch_affine, CR.branch_old
def branch_affine(Bf, L, capped=False, zs=None):
    if not any(k in LEV for k in ('KL', 'CI')):
        return _aff0(Bf, L, capped, zs)
    if capped:
        return _branch(const(2), smul(2*zs, PP))
    return _branch(sub(const(2), smul(Fr(4)/L, PP)), smul(2*Bf/L, PP))
def branch_old(kappa):
    if not any(k in LEV for k in ('KL', 'CI')):
        return _old0(kappa)
    L = 6*kappa
    return _branch(sub(const(2), smul(Fr(4)/L, PP)), smul(Fr(2)/L, PP))
CR.branch_affine = branch_affine
CR.branch_old = branch_old

_rp1 = CR.return_poly
def return_poly2(br, G, d, C):
    eta4 = Fr(LEV.get('eta4', 0))
    if not eta4:
        return _rp1(br, G, d, C)
    # eta4: E -> E - eta4 d/4  (same as dE = -eta4 d /4, d-dependent)
    old = LEV.get('dE', 0)
    LEV['dE'] = Fr(old) - eta4*d/4
    try:
        return _rp1(br, G, d, C)
    finally:
        LEV['dE'] = old
CR.return_poly = return_poly2
