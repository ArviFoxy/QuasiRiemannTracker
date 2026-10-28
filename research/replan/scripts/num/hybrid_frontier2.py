import numpy as np, collections
from hybrid_gates import gates
def worst_gate(B0,L0,c0,B,L,c,A,D,n=201):
    s0,v,q,u,G = gates(B0,L0,c0,B,L,c,A,D,n)
    res = {k: float(arr.min()) for k,arr in G.items()}
    return res
Agrid = np.linspace(0.3,1.6,53); Dgrid = np.linspace(0,300,61)
par=(0.9959,2.5,0.1); L=2.45; c=0.1
for B in [0.9930,0.9934,0.9935,0.9936,0.9938,0.9940]:
    fails = collections.Counter(); bestscore=-9; bestAD=None; feasible=0
    for A in Agrid:
        for D in Dgrid:
            res = worst_gate(*par,B,L,c,A,D)
            bad = [k for k,m in res.items() if m<=1e-6]
            if not bad: feasible+=1
            for k in bad: fails[k]+=1
    print("B=%.4f: feasible (A,D) count = %d ; most frequent failing gates: %s" % (B, feasible, fails.most_common(4)))
