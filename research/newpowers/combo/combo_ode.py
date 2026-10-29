"""Model: density chain (continuum, T-A's ode2 + exact return) with the HIGH gain replaced by
   mode 'ours'  : repeated-mark gainK (PR 76, K = 8)                 [T-A baseline]
   mode 'pr93'  : PR 93's retained-slope saving (nu - k + 17/200) * min(S, Q/10), nu in [13/20, 3/4], 0 below
   mode 'max'   : max of the two
   mode 'pr93x' : PR 93's saving extended below 13/20 with slope max(k - 17/200, 1001/2000)   (NOT proved; what-if)
   mode 'maxx'  : max(ours, pr93x)
   mode 'pr93a' : PR 93's adaptive price (AdaptivePrice.lean): retained slope k(nu) - c(q), c(q) = min(9/100, k(q) - 10011/20000),
                  q = live cut (= least nu of the gate), valid for q >= 29/50; saving (nu - k(nu) + c(q)) * min(S, Q/10)
   mode 'maxa'  : max(ours, pr93a)
usage: python3 combo_ode.py MODE BOOT DFAC floors"""
import sys, os, json, time
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ta'))
import gainc as GC
import ode2, run_ode2

MODE = sys.argv[1]
_orig = GC.gainK


def k(nu):
    return 10 * nu / (15 - 6 * nu)


def pr93(nu, S, Q, ext=False):
    nu = np.asarray(nu, dtype=float)
    kap = k(nu) - 17 / 200
    if ext:
        kap = np.maximum(kap, 1001 / 2000)
        ok = nu <= 0.75
    else:
        ok = (nu >= 13 / 20 - 1e-12) & (nu <= 0.75)
    sav = np.maximum(nu - kap, 0) * np.minimum(np.maximum(S, 0), np.maximum(Q, 0) / 10)
    return np.where(ok, sav, 0.0)


def pr93a(nu, S, Q):
    nu = np.asarray(nu, dtype=float)
    q = float(np.min(nu))
    if q < 29 / 50 - 1e-12:
        return np.zeros(np.broadcast(nu, np.asarray(S), np.asarray(Q)).shape)
    c = min(9 / 100, k(q) - 10011 / 20000)
    sav = np.maximum(nu - k(nu) + c, 0) * np.minimum(np.maximum(S, 0), np.maximum(Q, 0) / 10)
    return np.where(nu <= 0.75, sav, 0.0)


def gainK(nu, K, B, lam, h, S, Q, **kw):
    if MODE == 'pr93a':
        return pr93a(nu, S, Q) + 0 * np.asarray(B)
    if MODE == 'maxa':
        return np.maximum(_orig(nu, K, B, lam, h, S, Q, **kw), pr93a(nu, S, Q))
    if MODE == 'ours':
        return _orig(nu, K, B, lam, h, S, Q, **kw)
    if MODE == 'pr93':
        return pr93(nu, S, Q) + 0 * np.asarray(B)
    if MODE == 'pr93x':
        return pr93(nu, S, Q, ext=True) + 0 * np.asarray(B)
    o = _orig(nu, K, B, lam, h, S, Q, **kw)
    return np.maximum(o, pr93(nu, S, Q, ext=(MODE == 'maxx')))


GC.gainK = gainK
ode2.GC.gainK = gainK
boot = bool(int(sys.argv[2])); dfac = float(sys.argv[3])
floors = [float(x) for x in sys.argv[4].split(',')]
run_ode2.RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
os.makedirs(run_ode2.RES, exist_ok=True)
run_ode2.run_ode(1.0, boot, dfac, floors, tag='_' + MODE)
