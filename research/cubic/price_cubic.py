"""price_cubic.py -- R2 pricing (exact-return toolchain, floor 3/5, role split) of hypothetical cubic amplifier ledgers.

Runs a COPY of research/newpowers/r2 (scratch/cubic/r2copy) so that the theta cache writes stay in scratch.
usage: R2_TC=/home/user/QuasiRiemannTracker/research/newpowers/r3/tc python3 price_cubic.py tag [tag ...]
"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'r2copy'))
from ledger import Amp, SIMPLE, unit_payment, barrier_Lambda  # noqa: E402
from ode_amp import OdeAmp  # noqa: E402
import pricing2 as P2  # noqa: E402


def mk(name, e, c, r):
    return Amp(name, 1, 1, e, c, r, 1, "hyp")


CUB_SIMPLE = mk("cubic D^1 (1,3,1)", 1.0, 3.0, 1.0)
CUB_SQUARED = mk("cubic D^2 -> D^-1 (2,3,1)", 2.0, 3.0, 1.0)
SEX_DOUBLED = mk("sextic doubled (2,6,1)", 2.0, 6.0, 1.0)


def blend_c(phi):
    # fraction phi of the transferred width uses the cubic simple block, rest Sil's sextic (1,6,1): payments add (R2 s5.1)
    return mk("blend phi=%.4f" % phi, 1.0, 6.0 - 3.0 * phi, 1.0)


SC = {
    'base': lambda: OdeAmp([SIMPLE]),
    'cub131': lambda: OdeAmp([CUB_SIMPLE]),
    'cub231': lambda: OdeAmp([CUB_SQUARED]),
    'phi0.0138': lambda: OdeAmp([blend_c(0.0138)]),
    'phi0.02': lambda: OdeAmp([blend_c(0.02)]),
    'phi0.05': lambda: OdeAmp([blend_c(0.05)]),
    'phi0.10': lambda: OdeAmp([blend_c(0.10)]),
    'c5.85': lambda: OdeAmp([mk("c5.85", 1.0, 5.85, 1.0)]),
    'c5.8': lambda: OdeAmp([mk("c5.8", 1.0, 5.8, 1.0)]),
}

if __name__ == '__main__':
    tags = sys.argv[1:] or list(SC)
    for tag in tags:
        t0 = time.time()
        ode = SC[tag]()
        # chain shape diagnostics
        diag = {}
        for L in (2.5, 2.34, 2.2, 2.0):
            try:
                diag[str(L)] = (round(ode.B(L), 6), round(ode.qinf(L), 4), round(ode.slope(L), 5))
            except Exception:  # noqa: BLE001
                diag[str(L)] = None
        wall, res = P2.price_cd(ode, 0.60)
        row = dict(tag=tag, wall=wall, **(res or {}), diag=diag, secs=round(time.time() - t0))
        with open(os.path.join(HERE, 'price_cubic.jsonl'), 'a') as fh:
            fh.write(json.dumps(row) + '\n')
        print(json.dumps(row), flush=True)
