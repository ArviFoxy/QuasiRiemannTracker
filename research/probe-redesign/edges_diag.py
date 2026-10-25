import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model69 as M
from fractions import Fraction as Fr
from pick_theta2 import maxc, gap, edges2
nodes = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks', 'cchain_k8b.json')))
def face(i): n = nodes[i]; return (float(Fr(n['B'])), float(Fr(n['L'])), float(Fr(n['cap'])))
C, P = face(58), face(52)
FC = M.Face(C[0], C[1], 13/250, 'C'); FP = M.Face(P[0], P[1], 43/1000, 'P')
dl, pp = M.grid(401, 201)
res=[]
for h in np.linspace(0.790, 0.800, 11):
    c, o = maxc(FC, FP, h, 1/25, dl, pp)
    res.append((c,h)); print(f"h={h:.4f} theta={1-c:.9f}", flush=True)
c,h = max(res)
theta, ell, x, y, kappa = M.geometry(c, h)
print("best", 1-c, h, "ell",ell,"x",x,"y",y,"kappa",kappa)
Rs = M.count_envelope(kappa, dl, pp, (FC, FP), M.K_I_FINAL)
E, order = edges2(c, h, FP.B, FP.Lam, 1/25)
for name, d, Cc in E:
    e = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + dl/2 + dl*pp*(ell - Cc/2) + 0.75*d*Rs) - theta
    i = np.unravel_index(np.argmax(e), e.shape)
    print(f"{name:12s} d={d:.5f} C={Cc:.5f} max(E-theta)={e[i]:.3e} at delta={dl[i]:.4f} p={pp[i]:.4f} R={Rs[i]:.5f}")
