import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json, numpy as np
sys.path.insert(0, HERE)
import build_chain as BC
from gain_k import f_p
PS = np.array(sorted(set([0, 0.1, 0.2, 0.3, 0.35, 0.4, 0.42, 0.44] + list(np.linspace(0.45, 0.5, 21)))))
def gain_pmin(k, HP):
    if HP is None: HP = (1.0, BC.K_FB, 0.055)
    BH, LH, hH = HP
    def g(nu, S, Fp):
        return np.minimum.reduce([f_p(nu, S, Fp, p, k, plain='face', BL=(BH, LH, hH)) for p in PS])
    return g
BC.gain_half = gain_pmin
if __name__ == "__main__":
    k = int(sys.argv[1]); step = float(sys.argv[2])
    capf = lambda s: min(0.0549989, s + 0.016)
    piv = list(np.arange(0.0135, 0.04232, step)) + [0.04232]
    nodes = BC.build(k, piv, capf, verbose=True)
    json.dump(nodes, open(os.path.join(HERE, f'chainp_k{k}_{step}.json'), 'w'))
