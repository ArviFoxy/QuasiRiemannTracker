import numpy as np, collections
from hybrid_gates import gates
def run(par, L, c, Bs, Agrid, Dgrid):
    for B in Bs:
        fails = collections.Counter(); feasible=0; ex=None
        for A in Agrid:
            for D in Dgrid:
                s0,v,q,u,G = gates(*par,B,L,c,A,D,201)
                bad = [k for k,arr in G.items() if arr.min()<=1e-6]
                if not bad:
                    feasible+=1; ex=(round(float(A),3),round(float(D),1))
                for k in bad: fails[k]+=1
        print("  child (B=%.4f,L=%.2f,c=%.2f): feasible (A,D) = %d %s ; failing gates: %s" % (B,L,c,feasible, ex if ex else '', fails.most_common(3)))
Agrid = np.linspace(0.3,1.8,31); Dgrid = np.linspace(0,300,31)
print("step 1: parent (0.9999,2.58,0.12) -> L=2.50 c=0.10")
run((0.9999,2.58,0.12), 2.5, 0.1, [0.9950,0.9955,0.9959,0.9961,0.9963,0.9966,0.9970], Agrid, Dgrid)
