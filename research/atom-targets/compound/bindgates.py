import sys, json
sys.path.insert(0,'/home/user/QuasiRiemannTracker/research/repeated-marks')
from fractions import Fraction as Fr
import numpy as np
import cchain_k as CK
from ss_fb import gates_at
nodes = json.load(open('/home/user/QuasiRiemannTracker/research/repeated-marks/cchain_k8b.json'))
fl = lambda s: float(Fr(s))
K = 8
par = (1.0, CK.K_FB, 0.055)
for i, n in enumerate(nodes):
    B, L, q, cap, s = fl(n['B']), fl(n['L']), fl(n['q']), fl(n['cap']), n['pivot']
    if i >= len(nodes)-6 or i in (0, 10, 20, 30, 40):
        g_ = CK.gfun(par, K)
        # perturb: reduce Lam by 1e-5 relative at same pivot (B moves along pivot line)
        for tag, Lt in (('at', L), ('tighter', L*(1-2e-5))):
            Bt = par[0] - (par[1]-Lt)*s
            bx = (par[0]-Bt)/(par[1]-Lt)
            rows = []
            for b in (bx, cap):
                g = gates_at(b, Bt, Lt, q, *par, par, sched=CK.SCHED, K=CK.K_FB, gain_fn=g_, nnu=401)
                items = []
                for k, v in g.items():
                    if k in ('a','den','S'): continue
                    x = v[0] if isinstance(v, tuple) else v
                    items.append((x, k))
                items.sort()
                rows.append((round(b,5), [(k, f"{x:.2e}") for x,k in items[:3]]))
            print(i, s, tag, f"B={Bt:.6f} L={Lt:.6f} q={q:.4f}", rows)
    par = (B, L, cap)
