#!/usr/bin/env python3
"""
What the return alone would give if an atom were at its conjectured (diagonal) value.
Uses the float LP model of ../../atom-targets/targets.py with the faces held fixed, so these are
return-only effects (the chain would improve further through rho and the faces).
  long line diagonal : L(r) = 1 - delta r for r > 1          (aL = 6, bL = 0)
  slot cost halved : marked inverse slot cost 1, r + z <= 1  (sI = 1; far stronger than P1)
  both together
"""
import sys, os, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'atom-targets'))
import targets as T

def theta_star(P, lo=0.80, hi=0.8752, nd=226, npp=21):
    dl, pp = np.meshgrid(np.linspace(0.30, 0.75, nd), np.linspace(0.30, 0.5, npp), indexing='ij')
    R = T.count(dl, pp, P)
    for _ in range(40):
        mid = (lo + hi)/2
        if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
        else: lo = mid
    return hi

cases = [('base (float model)', {}),
         ('long line diagonal', dict(aL=6.0, bL=0.0)),
         ('long line 1% better slope (bL = 4.95)', dict(bL=4.95)),
         ('inverse slot cost halved, sI = 1', dict(sI=1.0)),
         ('long line diagonal + sI = 1', dict(aL=6.0, bL=0.0, sI=1.0))]
base = None
for name, mod in cases:
    P = dict(T.BASE); P.update(mod)
    th = theta_star(P)
    if base is None: base = th
    print(f"{name:42s} theta* = {th:.7f}   change {th - base:+.2e}", flush=True)
