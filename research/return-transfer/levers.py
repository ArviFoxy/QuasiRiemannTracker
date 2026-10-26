"""Hypothetical levers of the return, priced exactly on top of Lemma W (scan_windows.conf).

Each lever is a monkeypatch of cert_return; all are off by default (LEV = {}):
  'dC'      : add dC to the physical capacity C at the new edges (new_switch, new_kink, new_top)
  'Cfull'   : the numerator's selected slots save delta p C instead of delta p C / 2
  'Ctop'    : replace C at new_top by min(Ctop*d, face branch)  ('sp' style first branch only)
  'Cface_off': drop the face branch of C_N, i.e. C_N(d) = s_P d   (no B_P, L_P limit)
  'KL'      : long-line slope kL (5/6 = sixth-power amplification): L(t) = (1-kL) + (kL - delta) t
  'CI'      : inverse slot cost c_I (2 = Theorem 7.3): I(r) = 1 - delta(p' + (1-p') r), p' = 2p/c_I
  'dE'      : additive change of the return exponent E (any constant of NR6)
  'eta4'    : a saving eta on the class fourth moment: (sum |N|^4)^{1/4} -> U^{(1-eta)/4}
  'capC'    : the count face C's proved cap (default: base cap 3/40)
Run with QRH_K=9/2.  usage: python3 levers.py 'lever=value,...' ..."""
import sys
from fractions import Fraction as Fr
import base as B
import windows as W
import scan_windows as SW
CR = B.CR
const, sub, add, mul, smul, DEL, PP = CR.const, CR.sub, CR.add, CR.mul, CR.smul, CR.DEL, CR.PP

LEV = {}

# ---------- count lines with general kL, c_I and constant shifts ----------
def _branch(A, Z):
    """three-line crossing with I(r) = 1 - delta(p' + (1-p') r), P(m) = 1 - delta(A m + Z),
    L(t) = 1 - kL + (kL - delta) t (A, Z as in Lean ReturnFormulas; reduces to FR4/FR6 at kL = 5/6, c_I = 2)."""
    KL = LEV.get('KL', Fr(5, 6)); CI = LEV.get('CI', Fr(2))
    Vp = sub(const(KL), DEL)
    pp = smul(2/Fr(CI), PP)
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

# ---------- return polynomial ----------
_rp0 = CR.return_poly
def return_poly(br, G, d, C):
    if 'dC' in LEV and C is not None:
        C = C + LEV['dC']
    half = Fr(1) if LEV.get('Cfull') else Fr(1, 2)
    eta4 = LEV.get('eta4', Fr(0)); dE = LEV.get('dE', Fr(0))
    Eb = add(const(Fr(1, 2) + 13*G['h']/75 - G['y']/2 - G['ell']/2 - Fr(9, 100)*d - eta4*d/4 + dE),
             smul(Fr(1, 2), DEL), smul(G['ell'] - half*C, mul(DEL, PP)))
    return sub(mul(br['J'], sub(const(G['theta'] - CR.R0), Eb)), smul(Fr(3, 4)*d, br['N']))
CR.return_poly = return_poly

# ---------- capacity ----------
_edges0 = CR.edges
def edges(G, BP, LP):
    E = _edges0(G, BP, LP)
    if LEV.get('Cface_off'):
        y, sP = G['y'], G['sP']
        out = []
        for name, d, C in E:
            if name.startswith('new'):
                C = sP*d
            out.append((name, d, C))
        E = out
    return E
CR.edges = edges

def theta(spec, lev):
    global LEV
    LEV = dict(lev)
    kv = dict(x.split('=') for x in spec.split(',') if x)
    W.JOIN = kv.pop('join', 'crossover')
    CR.M_MINUS = Fr(kv.pop('mminus', '0'))
    capC = kv.pop('capC', None)
    P = B.params(','.join(f'{k}={v}' for k, v in kv.items()))
    conf = SW.conf(P)
    if capC is not None:
        cw = Fr(capC) - Fr(1, 10**4)
        conf['C'] = dict(aff=[cw], cap=[P['sC'], cw, cw - Fr(5, 10**4), cw - Fr(2, 10**3), Fr(3, 40) - Fr(1, 10**4)])
    W.CONF = conf
    return B.theta_star(P, lo=8680000)

if __name__ == '__main__':
    for a in sys.argv[1:]:
        lev = {}; spec = []
        for kv in a.split(','):
            if not kv: continue
            k, v = kv.split('=')
            if k in ('dC', 'KL', 'CI', 'dE', 'eta4', 'Cfull', 'Cface_off'):
                lev[k] = Fr(v)
            else:
                spec.append(kv)
        print(a, theta(','.join(spec), lev), flush=True)

# ---------- old-branch count shift (candidate 2: a better old count) ----------
# 'dRold': R_old -> R_old - dRold  (N_old -> N_old - dRold * J_old)
_old_cur = CR.branch_old
def branch_old_shift(kappa):
    br = _old_cur(kappa)
    s = LEV.get('dRold')
    if s:
        br = dict(br); br['N'] = sub(br['N'], smul(s, br['J']))
    return br
CR.branch_old = branch_old_shift
