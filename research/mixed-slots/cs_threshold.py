"""Mixed prime/plain slots (architecture agent, round 4): how cheap must a plain mark be?

Toy count model (the agent's `fresh/model.py` and `fresh/mixed.py`, made honest in two ways):
* one shared P-line budget: 2m + Lam*zP + cS*zS <= B (the face B, not 1);
* plain slots get I-line marks only if IPLAIN is set (cost 2, like prime marks in the MI).
Prime slots carry length f*ell, plain slots (1-f)*ell. The adversary picks (delta, pP, pS).
Prints theta(f, cS) - theta(1, -) for a grid of cS. Only differences are meaningful (the toy's
absolute theta is off by ~1e-5).
usage: python3 cs_threshold.py [IPLAIN=0|1]"""
import sys, itertools
import numpy as np
from scipy.optimize import brentq

B, LAM, H, C = 0.951, 2.77, 0.80, 0.033
T = np.linspace(1.0, 1.5, 251)[:, None]
S = np.linspace(0, 1, 401)[None, :]
RR = (T - 0.5) + 0.5*S
MM = T - RR
IPLAIN = len(sys.argv) > 1 and sys.argv[1] == '1'
UNIT = len(sys.argv) > 2 and sys.argv[2] == 'unit'

def count(delta, pP, pS, lP, lS, cS):
    supP, supS = lP/H, lS/H
    # I line: MI budget r + 2(zP + zS) <= 1 (plain marks only if IPLAIN)
    room = np.maximum(0, (1 - RR)/2)
    zPi = np.minimum(room, supP)
    zSi = np.minimum(np.maximum(0, room - zPi), supS) if IPLAIN else 0*RR
    zSi2 = np.minimum(room, supS) if IPLAIN else 0*RR
    zPi2 = np.minimum(np.maximum(0, room - zSi2), supP)
    gI = np.maximum(pP*zPi + pS*zSi, pP*zPi2 + pS*zSi2)
    I = np.where(RR < 1, 1 - delta*RR - 2*delta*gI, 1/6 + (5/6 - delta)*RR)
    # P line: shared face budget, fill the better rate first (pP/LAM vs pS/cS), then the other
    roomP = np.maximum(0, B - 2*MM)
    def fill(first_rate_cost, first_sup, second_cost, second_sup):
        z1 = np.minimum(roomP/first_rate_cost, first_sup)
        z2 = np.minimum(np.maximum(0, roomP - first_rate_cost*z1)/second_cost, second_sup)
        return z1, z2
    zPa, zSa = fill(LAM, supP, cS, supS)
    zSb, zPb = fill(cS, supS, LAM, supP)
    if UNIT:
        room1 = np.maximum(0, 1 - 2*MM)
        zSb = np.minimum(room1/cS, supS)
        zPb = np.minimum(np.maximum(0, B - 2*MM - cS*zSb)/LAM, supP)
        zPa = np.minimum(roomP/LAM, supP)
        zSa = np.minimum(np.maximum(0, 1 - 2*MM - LAM*zPa)/cS, supS)
    gP = np.maximum(pP*zPa + pS*zSa, pP*zPb + pS*zSb)
    P = 1 - 2*delta*MM - 2*delta*gP
    cross = np.max(np.minimum(I, P), axis=1)
    return np.min(np.maximum(cross, 1/6 + (5/6 - delta)*T[:, 0]))

def theta(f, cS):
    deltas = np.linspace(0.02, 0.75, 74)
    ps = [0, 0.25, 0.5]
    def worst(ell):
        lP, lS = f*ell, (1 - f)*ell
        w = -9
        for d in deltas:
            for pP, pS in itertools.product(ps, ps):
                if f == 1 and pS > 0: continue
                R = count(d, pP, pS, lP, lS, cS)
                v = 0.75*ell + d/2 + d*(pP*(lP - C*f/2) + pS*lS) + 0.75*H*R
                w = max(w, v)
        return w
    ell = brentq(lambda e: worst(e) - (5/12 + 5*H/12), 0.1, 0.25, xtol=1e-9)
    return 11/12 - ell/4

if __name__ == '__main__':
    base = theta(1.0, LAM)
    print(f"IPLAIN={IPLAIN} UNIT={UNIT} baseline theta={base:.7f}", flush=True)
    for f in (0.9, 0.8):
        for cS in (2.77, 2.6, 2.4, 2.2, 2.0, 1.5, 1.0):
            print(f"f={f:.2f} cS={cS:.2f} dtheta={theta(f, cS) - base:+.2e}", flush=True)
