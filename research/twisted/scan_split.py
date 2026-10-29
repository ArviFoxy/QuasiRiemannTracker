"""scan_split.py -- full role-split scan along a (twisted) continuum chain, exact six-branch return (TA toolchain).
theta*(C,P) = f(C) + g(P) (separable to ~2e-9, lemmaW.md), so: (1) scan count faces C over the whole chain with P fixed,
(2) scan physical faces P with the best C, (3) refine both, (4) final theta at 1e-9.
Usage: python3 scan_split.py KAPPA KROOM [floor]     (KAPPA >= 0.5716 gives the untwisted baseline)
"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'ta'))
import numpy as np
import exact
from twisted_ode import TwistedChain

P_REF = (2.2478, 0.9855194744739441)         # base physical face (TA), used while scanning C


def th(C, P, unit=10**8, guess=0.87385):
    r = exact.theta_exact(C[1], C[0], P[1], P[0], guess=guess, unit=unit, span=300 if unit == 10**8 else 400)
    return None if r is None else r[0]


def scan(kappa, kroom, floor=0.5, log=print):
    t0 = time.time()
    ch = TwistedChain(kappa=kappa, kroom=kroom)
    wall = ch.wall(floor) + 1e-6
    L0 = ch.L0 - 1e-6
    face = lambda L: (L, ch.B(L))
    grid = list(np.linspace(wall, min(L0, 2.55), 28))
    if ch.Lsw < L0:
        grid += [ch.Lsw + d for d in (-0.004, -0.002, 0.0, 0.002, 0.004) if wall <= ch.Lsw + d <= L0]
    grid = sorted(set(round(x, 7) for x in grid))
    # (1) count scan
    fC = {}
    for L in grid:
        fC[L] = th(face(L), P_REF)
    good = {L: v for L, v in fC.items() if v is not None}
    LC = min(good, key=good.get)
    step = (grid[-1] - grid[0]) / 27
    for d in (-step / 2, step / 2, -step / 4, step / 4, -step / 8, step / 8):
        L = LC + d
        if wall <= L <= L0 and round(L, 7) not in fC:
            fC[round(L, 7)] = th(face(L), P_REF)
    good = {L: v for L, v in fC.items() if v is not None}
    LC = min(good, key=good.get)
    C = face(LC)
    log('kappa %.3f  count scan done: LC=%.4f BC=%.6f theta(C,Pref)=%.8f  [%.0fs]' % (kappa, C[0], C[1], good[LC], time.time() - t0))
    # (2) physical scan with best C
    gP = {}
    for L in grid:
        gP[L] = th(C, face(L))
    goodP = {L: v for L, v in gP.items() if v is not None}
    LP = min(goodP, key=goodP.get)
    for d in (-step / 2, step / 2, -step / 4, step / 4, -step / 8, step / 8):
        L = LP + d
        if wall <= L <= L0 and round(L, 7) not in gP:
            gP[round(L, 7)] = th(C, face(L))
    goodP = {L: v for L, v in gP.items() if v is not None}
    LP = min(goodP, key=goodP.get)
    P = face(LP)
    final = th(C, P, unit=10**9, guess=goodP[LP])
    out = dict(kappa=kappa, kroom=kroom, floor=floor, theta=final, C=dict(L=C[0], B=C[1], s0=ch.slope(C[0])),
               P=dict(L=P[0], B=P[1], s0=ch.slope(P[0])), wall=wall, Lswitch=ch.Lsw, Bswitch=ch.Bsw,
               fC=sorted(fC.items()), gP=sorted(gP.items()), secs=time.time() - t0)
    log(json.dumps({k: v for k, v in out.items() if k not in ('fC', 'gP')}, default=str))
    return out


if __name__ == '__main__':
    kappa = float(sys.argv[1]); kroom = float(sys.argv[2])
    floor = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
    o = scan(kappa, kroom, floor, log=lambda s: print(s, flush=True))
    json.dump(o, open(os.path.join(HERE, 'scan_k%.3f_r%.3f_f%.2f.json' % (kappa, kroom, floor)), 'w'), indent=1, default=str)
