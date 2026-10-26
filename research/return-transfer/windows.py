"""Count-candidate windows of the return (FR3/FR8), opened up to the faces' proved domains.

Collet's count uses, per face, one affine branch with width window s_+ and one capped branch with
z_* = s_+ - eta, each admitted only when the crossing plain length m_* lies in
[m_L, m_U] (m_L >= m_- = 2/5).  The count's moment is the broad face [0, 1/2] x [0, cap]
(Lean: count_from_piecewise_moments needs only 0 <= mLo), so the windows are a certificate choice.

This module replaces CR.candidates by a configurable list:
  CONF = {'C': dict(aff=[s_+ ...], cap=[z_* + eta ...], weak=[j ...]), 'P': ...}
and sets CR.M_MINUS.  Every listed branch is a valid count where admitted, so the count is the
admitted minimum over the list (monotone: more branches never hurt)."""
import os
from fractions import Fraction as Fr
import base as B
CR = B.CR

CONF = None   # None: Collet's candidates (one affine + one capped per face at its s_+, weak j = 0..8)

def candidates(faces, kap):
    if CONF is None:
        return _orig(faces, kap)
    out = [('old', CR.branch_old(kap), None)]
    for name, (Bf, L, s_plus) in faces.items():
        c = CONF.get(name, {})
        for j in c.get('weak', [0]):
            Bj = Bf - Fr(j, 4000)
            for s in c.get('aff', [s_plus]):
                out.append((f'{name}{j}a{float(s):.4f}', CR.branch_affine(Bj, L), (Bj, L, Fr(s), False)))
            for s in c.get('cap', [s_plus]):
                zs = Fr(s) - CR.ETA
                out.append((f'{name}{j}c{float(s):.4f}', CR.branch_affine(Bj, L, capped=True, zs=zs),
                            (Bj, L, Fr(s), True)))
    return out

_orig = CR.candidates
CR.candidates = candidates

# ---- the tail join -------------------------------------------------------------------------
# Collet joins every improved plain line to the natural one at the fixed m_H = (1 - K s_-)/2, where
# the face is still WIDER than the natural face; the jump is paid by the FR8 test 'N-tail'
# (R >= natural line at m_H).  The plain witness argument only needs a continuous decreasing
# envelope on [m_*, 1/2].  Joining at the crossover m_X where the face width (B - 2m)/L equals
# the natural width (1 - 2m)/K removes the jump: for m in [m_*, m_X] use the face, for m >= m_X
# the natural face; both lines are decreasing (slope -2 delta (1 - 2p/L) < 0) and agree at m_X.
# JOIN = 'collet' keeps FR8 verbatim; JOIN = 'crossover' uses, per branch,
#   m_U = min(1/2 - eta, m_X - eta, capped: (B - L z_*)/2 - eta),  N-tail at m_X with width w_X,
#   no m_+ = 11/25 and no lower width window s_- (the face holds for all 0 <= s <= cap).
JOIN = 'collet'
_adm0 = CR.admission_polys
def admission_polys(br, Bf, L, s_plus, capped):
    if JOIN == 'collet':
        return _adm0(br, Bf, L, s_plus, capped)
    ETA, K = CR.ETA, CR.K_I
    mX = (K*Bf - L)/(2*(K - L))          # face width = natural width
    wX = (1 - 2*mX)/K
    if capped:
        zs = s_plus - ETA
        mL = CR.M_MINUS + ETA
        mU = min(Fr(1, 2) - ETA, mX - ETA, (Bf - L*zs)/2 - ETA)
    else:
        mL = max(CR.M_MINUS + ETA, (Bf - L*(s_plus - ETA))/2 + ETA)
        mU = min(Fr(1, 2) - ETA, mX - ETA)
    D, A, C0, U, J, N, T, Rn, Mn = (br[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'Rn', 'Mn'))
    sub, smul, mul, add, const, DEL, PP, dp = CR.sub, CR.smul, CR.mul, CR.add, CR.const, CR.DEL, CR.PP, CR.dp
    DJ = mul(D, J)
    polys = {
        'D': D, 'A': A, 'C0': C0, 'J': J, 'T-J': sub(T, J),
        '1.2499J-T': sub(smul(Fr(12499, 10000), J), T),
        'Rn-23/37DJ': sub(Rn, smul(Fr(23, 37), DJ)), 'DJ-Rn': sub(DJ, Rn),
        'Mn-mLDJ': sub(Mn, smul(mL, DJ)), 'mUDJ-Mn': sub(smul(mU, DJ), Mn),
        'N-tail': sub(N, mul(add(const(1), smul(-2*mX, DEL), smul(-2*wX, mul(DEL, PP))), J)),
        'UJp-UpJ': sub(mul(U, dp(J)), mul(dp(U), J)),
    }
    if capped:
        polys['cap'] = smul(zs - ETA, DJ)
    scal = {'wX>0': wX - ETA, 'mX<1/2': Fr(1, 2) - mX, 'L<K': K - L}
    return polys, scal
CR.admission_polys = admission_polys

def run(spec_list, P, mminus=Fr(2, 5)):
    global CONF
    out = []
    for label, conf in spec_list:
        CONF = conf
        CR.M_MINUS = Fr(mminus)
        t = B.theta_star(P, lo=8690000)
        out.append((label, t))
        print(f"{label}: theta* = {t}", flush=True)
    return out

if __name__ == '__main__':
    import sys
    P = B.params(sys.argv[1] if len(sys.argv) > 1 else '')
    capw = P['cap'] - Fr(1, 10**4)        # largest window strictly inside the proved face cap
    specs = [
        ("Collet windows, m_-=2/5", None),
        ("m_-=0, Collet windows", None),
        ("m_-=0, affine s_+=cap, capped z at 29/500 and cap", {
            'C': dict(aff=[capw], cap=[Fr(29, 500), capw]),
            'P': dict(aff=[capw], cap=[Fr(43, 1000), capw])}),
    ]
    CONF = None; CR.M_MINUS = Fr(2, 5)
    print("Collet windows, m_-=2/5: theta* =", B.theta_star(P, lo=8690000), flush=True)
    CR.M_MINUS = Fr(0)
    print("m_-=0, Collet windows: theta* =", B.theta_star(P, lo=8690000), flush=True)
    run(specs[2:], P, mminus=Fr(0))
