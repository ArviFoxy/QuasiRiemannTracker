"""Re-verify every node of a k-copy chain with the exact amplitude-minimized HIGH gain
G = min_p f_p (p-grid 401), six-facet form with HIGH parent = LOW parent."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json, numpy as np
sys.path.insert(0, HERE)
from ss_fb import gates_at, minres
from replay import SCHED, K_FB
from gain_k import f_p

PS = np.linspace(0, 0.5, 401)
def gain_pmin(k, HP):
    BH, LH, hH = HP
    def g(nu, S, Fp):
        vals = [f_p(nu, S, Fp, p, k, plain='face', BL=(BH, LH, hH)) for p in PS]
        return np.minimum.reduce(vals)
    return g

def check(chain, k, start=(1.0, K_FB, 0.055), bud='O'):
    par = start; worst = (1, None)
    for i, n in enumerate(chain):
        B0, L0, h0 = par
        bx = (B0-n['B'])/(L0-n['L'])
        for b in (bx, n['cap']):
            g = gates_at(b, n['B'], n['L'], n['q'], B0, L0, h0, par, sched=SCHED[bud], K=K_FB,
                         gain_fn=gain_pmin(k, par), nnu=401)
            m = minres(g)
            if m[0] < worst[0]: worst = (m[0], (i, round(n['bx'], 5), m[1], round(b, 5)))
        par = (n['B'], n['L'], n['cap'])
    return worst

if __name__ == "__main__":
    ch = json.load(open(sys.argv[1])); k = int(sys.argv[2])
    print("nodes", len(ch), "worst reserve with exact p-min gain:", check(ch, k))
