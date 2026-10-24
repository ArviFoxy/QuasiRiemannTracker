import sys, json, numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model69 as M
from pick_theta2 import maxc
ch = json.load(open('cchain_k2.json'))
nC = ch[-1]; nP = min(ch, key=lambda n: abs(n['pivot'] - 0.0395))
print("C", nC, "\nP", nP)
from fractions import Fraction as Fr
FC = M.Face(float(Fr(nC['B'])), float(Fr(nC['L'])), 11/250, 'C'); FP = M.Face(float(Fr(nP['B'])), float(Fr(nP['L'])), 43/1000, 'P')
dl, pp = M.grid(601, 301)
best = (0, None)
for h in np.linspace(0.79970, 0.80000, 13):
    c, order = maxc(FC, FP, h, 1/25, dl, pp)
    if c > best[0]: best = (c, h, order)
    print(f"h={h:.6f} c={c:.11f} order={order}", flush=True)
print("best", best)
