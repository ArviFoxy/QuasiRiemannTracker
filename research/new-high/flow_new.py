"""Mixed-step continuum flow (as ../mixed-step/mixed_family.py flow) with a pluggable HIGH gate.

The full float gate set of ../faceless-chain/gates.py with the mixed LOW step of
../mixed-step/continuum_mixed.py (c = 6: den3 = 1 + q - 6qB/L).  The HIGH gate is replaced by
hgate.high_gate_gen with a model from models.py.

q modes:
  grid : q on continuum_mixed.QGRID (largest feasible first), exactly as the published flow;
  cont : q = (1 - DEN)/(6B/L - 1) (the largest q with den3 = DEN), then bisection on L only.
usage: python3 flow_new.py OUT.json MODEL [qmode] [mh] [cap] [s_end] [ds]
"""
import sys, os, json, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'faceless-chain'))
sys.path.insert(0, os.path.join(HERE, '..', 'mixed-step'))
_argv = sys.argv[:]
sys.argv = ['x', '/dev/null', '6']
import continuum_mixed as CM
sys.argv = _argv
G = CM.G
import hgate as HG
import models as MD
from fractions import Fraction as Fr

DEN = 1e-5
QTOP = 0.749


def install(model_name):
    model = MD.MODELS[model_name]
    if model is None:
        return  # original gates.high_gate
    def hg(n, low, h, b, nu, p, copies=8):
        return HG.high_gate_gen(n, low, h, b, nu, p, copies, model=model, basics=G.basics)
    G.high_gate = hg


def ok_cont(s, E, L, mh, cap, fees=G.FINE):
    B = E + L*s
    x = 6*B/L - 1
    if x <= 0 or B < 22/23 or B > 1:
        return False
    q = min((1 - DEN)/x, QTOP)
    if not (0.5 <= q < 0.75):
        return False
    n = G.node(B, L, cap, q, fees)
    for b in (s, cap):
        m = G.margins(n, n, n, b)
        if m['scalar'] <= 0 or m['sector'] <= 0 or m['high'] <= mh:
            return False
    return True


def min_slope_cont(s, E, Lguess, mh, cap):
    Lmax = (1 - E)/s*(1 - 1e-12)
    hi = min(Lguess*1.02, Lmax)
    if not ok_cont(s, E, hi, mh, cap):
        for x in np.linspace(hi, Lmax, 80)[1:]:
            if ok_cont(s, E, x, mh, cap):
                hi = x; break
        else:
            return None, None
    lo = hi*0.98
    while lo > 0.3 and ok_cont(s, E, lo, mh, cap):
        hi = lo; lo *= 0.98
    for _ in range(40):
        mid = 0.5*(lo + hi)
        if ok_cont(s, E, mid, mh, cap): hi = mid
        else: lo = mid
    B = E + hi*s
    return hi, min((1 - DEN)/(6*B/hi - 1), QTOP)


def run(out, model_name, qmode='cont', mh=1e-4, cap=0.075, s_end=0.062, ds=5e-4, verbose=True):
    install(model_name)
    fan = json.load(open(os.path.join(HERE, '..', 'mixed-step', 'fan_16_1000.json')))
    last = fan[-1]
    s0 = 0.016; L = float(Fr(last['L'])); E = float(Fr(last['B'])) - L*s0
    s = s0
    if qmode == 'grid':
        CM.ok_node_q.__defaults__ = (mh, G.FINE, cap)
        ms = lambda s, E, L: CM.min_slope(s, E, L)
    else:
        ms = lambda s, E, L: min_slope_cont(s, E, L, mh, cap)
    rows = []; t0 = time.time()
    while s <= s_end + 1e-12:
        Ln, q = ms(s, E, L)
        if Ln is None:
            print('infeasible at', s, flush=True); break
        L = Ln
        rows.append(dict(s=s, E=E, L=L, q=q, B=E + L*s))
        if verbose:
            print(f"s={s:.5f} E={E:.7f} L={L:.6f} B={E + L*s:.7f} q={q:.4f} t={time.time()-t0:.0f}", flush=True)
        json.dump(rows, open(out, 'w'), indent=0)
        Lm, _ = ms(s + ds/2, E - L*ds/2, L)
        E -= (Lm if Lm is not None else L)*ds
        s = round(s + ds, 12)
    return rows


if __name__ == '__main__':
    out = sys.argv[1]; name = sys.argv[2]
    qmode = sys.argv[3] if len(sys.argv) > 3 else 'cont'
    mh = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-4
    cap = float(sys.argv[5]) if len(sys.argv) > 5 else 0.075
    s_end = float(sys.argv[6]) if len(sys.argv) > 6 else 0.062
    ds = float(sys.argv[7]) if len(sys.argv) > 7 else 5e-4
    run(out, name, qmode, mh, cap, s_end, ds)
