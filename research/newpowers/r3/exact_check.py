"""EXACT (Bernstein-cover, Fractions) verification of the new column-excess / long-line shift levers priced by the pointwise model.
The count branch polynomials of tc/cert_return.py are re-derived for
   eI : inverse line  I(r) = 1 - delta r - (2 delta p / c_I)(1 - r + eI)            (r + c_I z <= 1 + eI)
   sL : long line     L(t) = 1 - delta + (5/6-delta)(t-1) - sL                     (e.g. sL = (5/6) e/h from a Lemma-17.1 diagonal extension)
   (all derived from the same crossing algebra: t* J = T + sL D - delta pp eI A_P ,  N = N0 - a delta pp eI A_P - sL delta A_I A_P ,
    r* D J = A_P (t* J) + (Z - pp(1+eI)) J ,  m* D J = D (t* J) - r* D J ;  A_I = 1 - pp, pp = 2p/c_I, A_P = A.)
Usage: python3 exact_check.py            (a few minutes)
"""
import os, sys, time
os.environ.setdefault('QRH_K', '9/2')
HERE = os.path.dirname(os.path.abspath(__file__)); TC = os.path.join(HERE, 'tc')
sys.path.insert(0, TC); os.chdir(TC); sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import cert_return as CR
import pr86, best
from lowfloor_greedy import face, base

const, sub, add, mul, smul, DEL, PP = CR.const, CR.sub, CR.add, CR.mul, CR.smul, CR.DEL, CR.PP
LEV = {'eI': Fr(0), 'sL': Fr(0)}

def _branch(A, Z):
    eI, sL = Fr(LEV['eI']), Fr(LEV['sL'])
    Vp = sub(const(Fr(5, 6)), DEL)
    pp = PP                                  # c_I = 2
    D = add(A, sub(const(1), pp))
    C0 = sub(const(1), Z)
    U = mul(sub(const(1), pp), C0)
    J = add(mul(Vp, D), mul(mul(DEL, sub(const(1), pp)), A))
    T = add(J, mul(DEL, U))
    N = add(mul(sub(const(1), DEL), J), mul(mul(Vp, DEL), U))
    if eI:
        T = sub(T, smul(eI, mul(mul(DEL, pp), A)))
        N = sub(N, smul(eI, mul(mul(Vp, DEL), mul(pp, A))))
    if sL:
        T = add(T, smul(sL, D))
        N = sub(N, smul(sL, mul(mul(DEL, sub(const(1), pp)), A)))
    Rn = add(mul(A, T), mul(sub(Z, smul(1 + eI, pp)), J))
    Mn = sub(mul(D, T), Rn)
    return dict(D=D, A=A, C0=C0, U=U, J=J, N=N, T=T, Rn=Rn, Mn=Mn)

_aff0 = CR.branch_affine
def branch_affine(Bf, L, capped=False, zs=None):
    if not (LEV['eI'] or LEV['sL']):
        return _aff0(Bf, L, capped, zs)
    if capped:
        return _branch(const(2), smul(2 * zs, PP))
    return _branch(sub(const(2), smul(Fr(4) / L, PP)), smul(2 * Bf / L, PP))
CR.branch_affine = branch_affine

six = ['old', 'C', 'Ccap', 'C-7', 'P', 'Pcap']
WIDE = (Fr(87, 100), Fr(806, 1000), Fr(467, 1000), Fr(18, 100))

def th(cfg):
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873500000, step=1000)
    return None if r is None else r[0] / 1e9

def run(kc, kp, label, **lev):
    LEV['eI'] = Fr(lev.get('eI', 0)); LEV['sL'] = Fr(lev.get('sL', 0))
    fc, fp = face(kc), face(kp)
    cfg = base.copy(BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1], windows='lemmaW', branches=six, bounds=WIDE)
    t0 = time.time(); t = th(cfg)
    print('%-44s exact theta* = %.9f  (gap to bar %+.2e)  [%.0fs]' % (label, t, t - 0.8739358, time.time() - t0), flush=True)
    LEV['eI'] = Fr(0); LEV['sL'] = Fr(0)
    return t

if __name__ == '__main__':
    print('scenario A = lowered floor 0.60, count 73 / physical 38 ; scenario B = PR 86 chain 46/38 (exact covers)')
    run(73, 38, 'A  base')
    run(73, 38, 'A  eI = 7.3934e-4 (PM-needed; U units)', eI=Fr(73934, 10**8))
    run(73, 38, 'A  sL = 1.4e-4 ... shift of L line', sL=Fr(14, 10**5))
    # PM-needed fourth-power width w = 8.6547e-4 is equivalent (near t*=1.1427) to a constant shift w/3 = 2.885e-4
    run(73, 38, 'A  sL = w/3 = 2.8849e-4 (wL=8.6547e-4)', sL=Fr(28849, 10**8))
    run(73, 38, 'A  eI = 4.9e-4 + sL = 1.6e-4', eI=Fr(49, 10**5), sL=Fr(16, 10**5))
    run(46, 38, 'B  base')
    run(46, 38, 'B  eI = 1.3260e-3', eI=Fr(13260, 10**7))
    run(46, 38, 'B  sL = w/3 = 5.196e-4 (wL=1.5588e-3)', sL=Fr(5196, 10**7))
