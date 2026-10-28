"""EXACT verification of the joint column-excess lever (probe geometry x+y=1-ell+e, inverse line eI=e/h, long line sL=(5/6)e/h).
Probe geometry as in B1/energy_price.py: ell=(11-12 theta+e... ) generalised:  ell = 11/3 - 4 theta + e/3, y = h - 2 ell + e, x = 1+ell-h;
receipts that encode the old signal formula ('floor','floor_margin','small_saving') are dropped and h is scanned (as B1)."""
import os, sys, time
os.environ.setdefault('QRH_K', '9/2')
HERE = os.path.dirname(os.path.abspath(__file__)); TC = os.path.join(HERE, 'tc')
sys.path.insert(0, HERE); sys.path.insert(0, TC); os.chdir(TC); sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import cert_return as CR
import exact_check as EC            # patches CR.branch_affine with eI / sL
import pr86
from lowfloor_greedy import face, base

EPS = [Fr(0)]
def geometry(theta, h, BP, LP, sP=Fr(1, 25)):
    e = EPS[0]
    ell = Fr(11, 3) - 4 * theta + e / 3
    x = 1 + ell - h; y = h - 2 * ell + e
    kap = 2 * theta - 1
    d0 = Fr(1, 200); dplus = h + Fr(1, 10**10)
    ds = 2 * y / (1 + 6 * kap * sP); dk = 2 * y / (2 - BP + LP * sP)
    return dict(theta=theta, h=h, ell=ell, x=x, y=y, kap=kap, sP=sP, d0=d0, dplus=dplus, ds=ds, dk=dk)
CR.geometry = geometry
DROP = ('floor', 'floor_margin', 'small_saving')
WIDE = (Fr(87, 100), Fr(812, 1000), Fr(480, 1000), Fr(18, 100))
six = EC.six

def passes(cfg, th_units, h, unit=10**9):
    return pr86.certifiable(cfg.copy(th=Fr(th_units, unit), h=h))

def theta_h(cfg, h, unit=10**9, anchor=873960000, lo=873000000, step=1000):
    hi = anchor; n = 0
    while not passes(cfg, hi, h, unit):
        n += 1
        if n > 400: return None
        lo, hi = hi, hi + step
    while passes(cfg, lo, h, unit):
        hi = lo; lo -= 2000000
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if passes(cfg, mid, h, unit): hi = mid
        else: lo = mid
    return hi / 1e9

def run(kc, kp, e, probe=1, inv=1, lng=1, hs=('0.8052', '0.8054', '0.8056')):
    e = Fr(e)
    EPS[0] = e * probe
    EC.LEV['eI'] = (e / Fr(8054, 10000)) * inv
    EC.LEV['sL'] = (Fr(5, 6) * e / Fr(8054, 10000)) * lng
    fc, fp = face(kc), face(kp)
    cfg = base.copy(BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1], windows='lemmaW', branches=six, bounds=WIDE, drop_receipts=DROP)
    best = None
    for h in hs:
        t = theta_h(cfg, Fr(h))
        if t is not None and (best is None or t < best[0]): best = (t, h)
    EPS[0] = Fr(0); EC.LEV['eI'] = Fr(0); EC.LEV['sL'] = Fr(0)
    return best

if __name__ == '__main__':
    print('exact (h scanned, floor receipts dropped), scenario A = 73/38, bar 0.8739358')
    for label, e, kw in (('e=0', 0, {}),
                         ('probe only e=1.6619e-4', Fr(16619, 10**8), dict(inv=0, lng=0)),
                         ('probe+inverse e=1.2991e-4', Fr(12991, 10**8), dict(lng=0)),
                         ('probe+inverse+long e=8.8621e-5', Fr(88621, 10**9), {})):
        t0 = time.time(); b = run(73, 38, e, **kw)
        print('  %-34s exact theta* = %.9f at h=%s  gap %+.2e  [%.0fs]' % (label, b[0], b[1], b[0] - 0.8739358, time.time() - t0), flush=True)
