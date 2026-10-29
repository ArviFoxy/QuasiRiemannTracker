"""What-if variants of the per-class combination (perclass.py): ours (PR 76 repeated marks) vs PR 93's joint count.
   excl<p0> : HIGH rows have slot amplitude class p >= p0 (low classes excluded), PR 93 cut 1001/2000
   cut<c>   : PR 93's count available for delta = 2 p nu >= c (c < 1/2 is beyond PR 93's proof)
   dhall    : every class counted at J(nu, nu) = 1 - nu ("zero-forced marks": each HIGH row carries slots of slope nu)
usage: python3 perclass2.py MODE floors     [hypothetical inputs; numerical]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ta'))
import numpy as np
import gainc as GC
import ode2, run_ode2
MODE = sys.argv[1]
P0 = float(MODE[4:]) if MODE.startswith('excl') else 0.0
CUT = float(MODE[3:]) if MODE.startswith('cut') else 1001 / 2000
PG = np.linspace(P0, 0.5, 201)


def gainK(nu, K, B, lam, h, S, Q, **kw):
    nu, B, lam, h, S, Q = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, B, lam, h, S, Q)))
    n, b, l, hh, s, q = (x[..., None] for x in (nu, B, lam, h, S, Q))
    p = PG
    ours = GC.gainP(n, p, K, b, l, hh, np.maximum(s, 0), np.maximum(q, 0))
    slot = (1 - 2 * p) * n * np.maximum(s, 0)
    cnt_ours = ours - slot
    rho = 1 - 10 * n / (15 - 6 * n)
    if MODE == 'dhall':
        cnt93 = np.maximum(rho - (1 - n), 0) * np.maximum(q, 0) + 0 * p
    else:
        d = 2 * p * n
        J = 3 * (1 - d) * (1 - n) / (3 - n - 2 * d)
        cnt93 = np.where(d >= CUT, np.maximum(rho - J, 0) * np.maximum(q, 0), 0.0)
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
