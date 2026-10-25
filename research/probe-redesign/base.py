import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model69 as M
from fractions import Fraction as Fr
nodes = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks', 'cchain_k8b.json')))
def face(i): n = nodes[i]; return (float(Fr(n['B'])), float(Fr(n['L'])), float(Fr(n['cap'])))
C, P = face(58), face(52)
print("C face", C, "P face", P)
FC = M.Face(C[0], C[1], 13/250, 'C'); FP = M.Face(P[0], P[1], 43/1000, 'P')
from pick_theta2 import maxc, gap
dl, pp = M.grid(401, 201)
best=(0,None)
for h in np.linspace(0.7990, 0.8030, 21):
    c, o = maxc(FC, FP, h, 1/25, dl, pp)
    if c > best[0]: best=(c,h)
print("best theta", 1-best[0], "h", best[1], "ell", 4*best[0]-1/3)
