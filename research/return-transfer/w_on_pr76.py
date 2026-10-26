"""Lemma W on the certified PR 76 faces (no mixed step): faces of FinalReturn/ReturnConstants.lean as in
../strip-mine/atlas.py BASE, Collet's natural cost K (QRH_K unset), cap 549989/10^7, s_C = 13/250,
s_P = 9/200, h = 401/500, Lemma D mode (slope receipt dropped), dMinus field as given by QRH_DMINUS
(Collet's 3/4 by default).  usage: python3 w_on_pr76.py"""
import os, sys
from fractions import Fraction as Fr
assert os.environ.get('QRH_K') is None, "run without QRH_K (PR 76 uses Collet's natural cost)"
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)

BC = Fr(1272915379989926835893023, 1315333734400000000000000)
LC = Fr(3063363697870470065773, 1052266987520000000000)
BP = Fr(335106151738000623869543064163, 344806846470553600000000000000)
LP = Fr(631360617375411063383, 210453397504000000000)
CAP = Fr(549989, 10**7); H = Fr(401, 500); SC = Fr(13, 250); SP = Fr(9, 200)

_orig_cands, _orig_adm = CR.candidates, CR.admission_polys
MODE = {'W': False}
def admission_polys(br, Bf, L, s_plus, capped):
    if not MODE['W']:
        return _orig_adm(br, Bf, L, s_plus, capped)
    ETA, K = CR.ETA, CR.K_I
    mX = (K*Bf - L)/(2*(K - L)); wX = (1 - 2*mX)/K
    if capped:
        zs = s_plus - ETA; mL = ETA; mU = min(Fr(1, 2) - ETA, mX - ETA, (Bf - L*zs)/2 - ETA)
    else:
        mL = max(ETA, (Bf - L*(s_plus - ETA))/2 + ETA); mU = min(Fr(1, 2) - ETA, mX - ETA)
    D, A, C0, U, J, N, T, Rn, Mn = (br[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'Rn', 'Mn'))
    sub, smul, mul, add, const, DEL, PP, dp = CR.sub, CR.smul, CR.mul, CR.add, CR.const, CR.DEL, CR.PP, CR.dp
    DJ = mul(D, J)
    polys = {'D': D, 'A': A, 'C0': C0, 'J': J, 'T-J': sub(T, J), '1.2499J-T': sub(smul(Fr(12499, 10000), J), T),
             'Rn-23/37DJ': sub(Rn, smul(Fr(23, 37), DJ)), 'DJ-Rn': sub(DJ, Rn),
             'Mn-mLDJ': sub(Mn, smul(mL, DJ)), 'mUDJ-Mn': sub(smul(mU, DJ), Mn),
             'N-tail': sub(N, mul(add(const(1), smul(-2*mX, DEL), smul(-2*wX, mul(DEL, PP))), J)),
             'UJp-UpJ': sub(mul(U, dp(J)), mul(dp(U), J))}
    if capped: polys['cap'] = smul(zs - ETA, DJ)
    return polys, {'wX>0': wX - ETA, 'mX<1/2': Fr(1, 2) - mX, 'L<K': K - L}
CR.admission_polys = admission_polys

def ok(th, sC, sPp):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), H, (BC, LC, CAP), (BP, LP, CAP), verbose=False, sP=SP, sC=sC,
                               sPp=sPp, mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        return False
def ts(sC, sPp, lo=8740000, hi=8747700):
    if not ok(hi, sC, sPp): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, sC, sPp) else (mid, hi)
    return hi

if __name__ == '__main__':
    print('dMinus field:', CR.DMINUS, flush=True)
    MODE['W'] = False
    print('PR 76 return (Collet windows):', ts(SC, Fr(43, 1000)), flush=True)
    MODE['W'] = True
    w = CAP - Fr(1, 10**4)
    print('PR 76 faces + Lemma W (s_+ = cap - 1e-4, m_- = 0, crossover join):', ts(w, w), flush=True)
