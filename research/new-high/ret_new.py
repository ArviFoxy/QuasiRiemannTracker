"""Exact return (../mixed-step/ret_scan.py, Lemma D, dMinus > 1/2) with modified same-zero count lines.

The return's count (paper69 return.tex NR1/NR2, first-return.tex FR4-FR9) uses the SAME three witness
lines as the source HIGH count:
    I(r) = 1 - delta*(p' + (1 - p') r)        p' = 2p/cI   (inverse cap z = (1 - r)/cI; cI = 2: Thm 7.3)
    P(m) = 1 - 2 delta m - 2 delta p z(m)       (face)
    L(r) = (1 - kL) + (kL - delta) r            (kL = 5/6: long inverse moment (204))
Solving I(r*) = P(m*) = L(t*), r* + m* = t*, gives (derivation in REPORT.md, App. B)
    V = kL - delta, D = A + 1 - p', U = (1 - p') C0, J = V D + delta (1 - p') A,
    N = (1 - delta) J + V delta U, T = J + delta U, R_n = D (J - V C0), M_n = D T - R_n,
which reduces to FR4 for kL = 5/6, cI = 2 (checked numerically by test_ret_new.py).
Environment: QRH_KL (default 5/6), QRH_CI (default 2), QRH_TMAX (admission t* < TMAX, default 12499/10000).
usage: python3 ret_new.py 'BC=..,LC=..,BP=..,LP=..,sP=..,sC=..,cap=..,h=..' ...
"""
import sys, os
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mixed-step'))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
import ret_scan as RS
CR = RS.CR

KL = Fr(os.environ.get('QRH_KL', '5/6'))
CI = Fr(os.environ.get('QRH_CI', '2'))
TMAX = Fr(os.environ.get('QRH_TMAX', '12499/10000'))
const, sub, add, mul, smul, DEL, PP = CR.const, CR.sub, CR.add, CR.mul, CR.smul, CR.DEL, CR.PP

V = sub(const(KL), DEL)
PPr = smul(2/CI, PP)          # p' = 2p/cI


def _branch(Dfix, A, C0):
    """Dfix = D + p' (the part of D not involving the inverse line)."""
    D = sub(Dfix, PPr)
    U = mul(sub(const(1), PPr), C0)
    J = add(mul(V, D), mul(mul(DEL, sub(const(1), PPr)), A))
    N = add(mul(sub(const(1), DEL), J), mul(mul(V, DEL), U))
    T = add(J, mul(DEL, U))
    Rn = mul(D, sub(J, mul(V, C0)))
    Mn = sub(mul(D, T), Rn)
    return dict(D=D, A=A, C0=C0, U=U, J=J, N=N, T=T, Rn=Rn, Mn=Mn)


def branch_affine(B, L, capped=False, zs=None):
    if capped:
        return _branch(const(3), const(2), sub(const(1), smul(2*zs, PP)))
    A = sub(const(2), smul(Fr(4)/L, PP))
    return _branch(sub(const(3), smul(Fr(4)/L, PP)), A, sub(const(1), smul(2*B/L, PP)))


def branch_old(kappa):
    L = 6*kappa
    A = sub(const(2), smul(Fr(4)/L, PP))
    return _branch(sub(const(3), smul(Fr(4)/L, PP)), A, sub(const(1), smul(Fr(2)/L, PP)))


_adm = CR.admission_polys
def admission_polys(br, B, L, s_plus, capped):
    polys, scal = _adm(br, B, L, s_plus, capped)
    polys['1.2499J-T'] = sub(smul(TMAX, br['J']), br['T'])
    return polys, scal


if KL != Fr(5, 6) or CI != 2 or TMAX != Fr(12499, 10000) or os.environ.get('QRH_FORCE_PATCH'):
    CR.V = V
    CR.branch_affine = branch_affine
    CR.branch_old = branch_old
    CR.admission_polys = admission_polys

if __name__ == '__main__':
    for a in sys.argv[1:]:
        P = dict(RS.DEF)
        for kv in a.split(','):
            if kv: k, v = kv.split('='); P[k] = v
        P = {k: Fr(v) for k, v in P.items()}
        print(f"kL={KL} cI={CI} TMAX={TMAX}", a, RS.ts(P), flush=True)
