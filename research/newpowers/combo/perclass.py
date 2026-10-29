"""Per-class combination of our repeated-mark count and PR 93's joint count (what-if, PR 93 not merged).
For a HIGH class with slot amplitude delta = 2 p nu (p in [0,1/2]):
   ours   : (1-2p) nu S + nu (xi_P - xi0 Q)                        (PR 76 gainP)
   PR 93  : (1-2p) nu S + max(0, rho(nu) - J(nu, delta)) Q,  J = 3(1-delta)(1-nu)/(3-nu-2 delta),  if delta >= CUT
   combined class gain = (1-2p) nu S + max(both count terms);  gain = inf over p.
usage: python3 perclass.py MODE floors     MODE: comb (cut 1001/2000) | combx (cut 0: what-if without the amplitude cutoff)
                                           | combNU (cut 1001/2000, PR 93's count only for nu >= NU, e.g. comb0.58, comb0.65)"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ta'))
import numpy as np
import gainc as GC
import ode2, run_ode2
MODE = sys.argv[1]
CUT = 0.0 if MODE == 'combx' else 1001 / 2000
NUMIN = float(MODE[4:]) if MODE.startswith('comb') and len(MODE) > 5 and MODE[4] != 'x' else 0.0   # e.g. comb0.58
_orig = GC.gainK
PG = np.linspace(0.0, 0.5, 201)


def gainK(nu, K, B, lam, h, S, Q, **kw):
    nu, B, lam, h, S, Q = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, B, lam, h, S, Q)))
    shp = nu.shape
    n, b, l, hh, s, q = (x[..., None] for x in (nu, B, lam, h, S, Q))
    p = PG
    ours = GC.gainP(n, p, K, b, l, hh, np.maximum(s, 0), np.maximum(q, 0))        # (1-2p) nu S + nu(xi - xi0 Q)
    slot = (1 - 2 * p) * n * np.maximum(s, 0)
    cnt_ours = ours - slot
    d = 2 * p * n
    rho = 1 - 10 * n / (15 - 6 * n)
    J = 3 * (1 - d) * (1 - n) / (3 - n - 2 * d)
    cnt93 = np.where((d >= CUT) & (n >= NUMIN - 1e-12), np.maximum(rho - J, 0) * np.maximum(q, 0), 0.0)
    comb = slot + np.maximum(cnt_ours, cnt93)
    g = comb.min(axis=-1)
    ok = (nu > 0) & (nu <= 0.75) & (B >= GC.B_MIN) & (lam > 1) & (h >= 0) & (h <= 1)
    return np.where(ok, g, 0.0)


GC.gainK = gainK
ode2.GC.gainK = gainK
if __name__ == '__main__':
    floors = [float(x) for x in sys.argv[2].split(',')]
    run_ode2.RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
    os.makedirs(run_ode2.RES, exist_ok=True)
    run_ode2.run_ode(1.0, False, 0.999, floors, tag='_' + MODE)
