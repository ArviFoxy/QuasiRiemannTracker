"""Exact design of a marked density chain: float optimisation (T-A's chain2 model) -> exact rationals certified by
gen_hybrid's marked gate library (the structure `HybridGatesM qf` of `Submissions.arvi_density`).

Per step, from the exact parent G(B0, L0, c0):
  * child L = L0 - dL, child c = 1/10;
  * (A, D) from the float optimum at the exact parent (chain2.best_step), rounded to A = n/10^6, D = n/500;
  * B = the largest multiple of 1/UNIT for which every gate certifies (integer bisection on the numerator);
until no B certifies (the floor wall) or --max-steps. Every chosen step is certified once more with the exact self-checks.

usage: python3 design_chain.py --floor 1/2 --dL 1/200 --unit 100000000 -o steps.json [--max-steps N] [--resume steps.json]
"""
import argparse, json, math, os, sys, time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'newpowers', 'ta'))
import numpy as np
import gen_hybrid as GH
import chain2 as C2

BOOT = (Fr(99999, 100000), Fr(5143, 2000), Fr(1397, 10000))
CCHILD = Fr(1, 10)


def certifies(B0, L0, c0, B, L, c, A, D, floor, lib, verify=False):
    P = GH.Params(B0, L0, c0, B, L, c, A, D, floor=floor)
    try:
        GH.generate(P, lib=lib, verify=verify)
        return True
    except (ValueError, GH.InfeasibleGate):
        return False


def exact_step(B0, L0, c0, dL, A, D, floor, unit, lib, s_guess):
    """largest B = n/unit certifying with (A, D); None if nothing certifies in s0 <= c - 1e-4"""
    L = L0 - dL
    c = CCHILD

    def ok(n):
        return certifies(B0, L0, c0, Fr(n, unit), L, c, A, D, floor, lib)

    def n_of(s0):                      # B = B0 - s0 dL, rounded down
        return math.floor((B0 - Fr(s0) * dL) * unit)
    s_hi = s_guess * 1.04 + 2e-4
    n_lo = n_of(s_hi)                  # small B (large s0): should certify
    tries = 0
    while not ok(n_lo):
        tries += 1
        s_hi = s_hi * 1.15 + 1e-3
        if s_hi >= float(c) - 1e-4 or tries > 8:
            return None
        n_lo = n_of(s_hi)
    n_top = math.ceil(B0 * unit) - 1   # B < B0
    n_hi = min(n_of(max(s_guess * 0.97, 0.0)), n_top)
    if ok(n_hi):                       # the float optimum is conservative here: search further up
        step = max(1, n_hi - n_lo)
        n_lo = n_hi
        while True:
            cand = n_lo + step
            if cand > n_top:
                if n_lo == n_top or ok(n_top):
                    return Fr(n_top, unit)
                n_hi = n_top
                break
            if ok(cand):
                n_lo, step = cand, 2 * step
            else:
                n_hi = cand
                break
    while n_hi - n_lo > 1:
        mid = (n_lo + n_hi) // 2
        if ok(mid):
            n_lo = mid
        else:
            n_hi = mid
    return Fr(n_lo, unit)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--floor', default='1/2')
    ap.add_argument('--dL', default='1/200')
    ap.add_argument('--unit', type=int, default=10 ** 8)
    ap.add_argument('--max-steps', type=int, default=400)
    ap.add_argument('--resume', default=None)
    ap.add_argument('-o', '--output', required=True)
    a = ap.parse_args()
    floor, dL = Fr(a.floor), Fr(a.dL)
    lib = GH.marked_lib(GH.PR83_LIB)
    cfg = C2.Cfg(gain=1.0, floor=float(floor), dfac=0.999, boot=False, dL=float(dL), nu_mode='q')
    steps = []
    if a.resume:
        steps = json.load(open(a.resume))
    if steps:
        last = steps[-1]
        B0, L0, c0 = Fr(last['B']), Fr(last['L']), Fr(last['c'])
        guess = (math.log(float(Fr(last['A']))), math.log(float(Fr(last['D']))))
        s_guess = float((Fr(last['B0']) - Fr(last['B'])) / dL)
    else:
        B0, L0, c0 = BOOT
        guess, s_guess = (math.log(0.6), math.log(400.0)), None
    t0 = time.time()
    while len(steps) < a.max_steps:
        r = C2.best_step(cfg, float(B0), float(L0), float(c0), guess, s_guess)
        if r is None or r[0] >= 0.9:
            print(f'float model: no step from G({B0}, {L0}, {c0}) -- wall', flush=True)
            break
        s0f, Af, Df, _ = r
        A = Fr(round(Af * 10 ** 6), 10 ** 6)
        D = Fr(round(Df * 500), 500)
        B = exact_step(B0, L0, c0, dL, A, D, floor, a.unit, lib, s0f)
        if B is None:
            print(f'exact: no certified step from G({B0}, {L0}, {c0}) with A={A}, D={D} -- stop', flush=True)
            break
        L, c = L0 - dL, CCHILD
        if not certifies(B0, L0, c0, B, L, c, A, D, floor, lib, verify=True):
            raise SystemExit(f'self-check failed at step {len(steps) + 1}')
        s0 = (B0 - B) / dL
        steps.append(dict(B0=str(B0), L0=str(L0), c0=str(c0), B=str(B), L=str(L), c=str(c), A=str(A), D=str(D),
                          floor=str(floor), s0=float(s0), s0_float=s0f))
        print('[%3d] L=%.4f B=%.9f s0=%.6f (float %.6f, +%.2e) A=%s D=%s [%.0fs]' % (
            len(steps), float(L), float(B), float(s0), s0f, float(s0) - s0f, A, D, time.time() - t0), flush=True)
        json.dump(steps, open(a.output, 'w'), indent=1)
        B0, L0, c0 = B, L, c
        guess, s_guess = (math.log(Af), math.log(Df)), s0f
    print(f'{len(steps)} steps -> {a.output}', flush=True)


if __name__ == '__main__':
    main()
