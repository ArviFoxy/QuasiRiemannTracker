import numpy as np
from hybrid_gates import gates

def feasible(B0,L0,c0,B,L,c,A,D,eps=1e-6,n=401):
    s0,v,q,u,G = gates(B0,L0,c0,B,L,c,A,D,n)
    if c - s0 <= 0: return False, 'width_pos'
    worst=None
    for k,arr in G.items():
        m = arr.min()
        if m <= eps:
            if worst is None or m < worst[1]: worst=(k,m)
    if worst: return False, worst[0]
    return True, None

def best_B(B0,L0,c0,L,c, Bgrid, Agrid, Dgrid):
    for B in Bgrid:   # descending
        ok_any=False
        fails={}
        for A in Agrid:
            for D in Dgrid:
                ok,why = feasible(B0,L0,c0,B,L,c,A,D,n=201)
                if ok: return B,(A,D),None
                fails[why]=fails.get(why,0)+1
        last=fails
    return None,None,last

if __name__=='__main__':
    Agrid = np.linspace(0.3,1.6,27); Dgrid = np.linspace(0,300,31)
    # Step 2: parent (0.9959,2.5,0.1) -> child L=2.45, c=0.1
    for (name,par,L,c) in [("step2 L=2.45 c=0.10",(0.9959,2.5,0.1),2.45,0.1),
                           ("step2 L=2.45 c=0.09",(0.9959,2.5,0.1),2.45,0.09),
                           ("step2 L=2.45 c=0.11",(0.9959,2.5,0.1),2.45,0.11),
                           ("step2 L=2.40 c=0.10",(0.9959,2.5,0.1),2.40,0.1)]:
        Bgrid = np.arange(0.9959,0.985,-0.0001)
        B,AD,fails = best_B(*par,L,c,Bgrid,Agrid,Dgrid)
        print(name, "-> best B =", None if B is None else round(float(B),4), "(A,D)=", None if AD is None else (round(float(AD[0]),3),round(float(AD[1]),1)), "" if B is not None else fails)
