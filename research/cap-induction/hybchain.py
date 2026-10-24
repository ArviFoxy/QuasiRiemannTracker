"""Float model of the source chain with hybrid cap induction (Lemma F): on the width cells [bx,b1] the
LOW parent is the previous node (threshold q1 < L0/(6B0)); on [b1,h] it is the node itself at the
previous cap (threshold q2 < Lam/(6B)).  Pivots and caps follow cchain_k8b.json.
usage: python3 hybchain.py OUT.json"""
import sys, os, json, time, numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import cchain_k as CK
from ss_fb import gates_at, minres
RES=CK.RES
def res_at(b,B,Lam,q,par,HP,g_,nnu=201):
    return minres(gates_at(b,B,Lam,q,par[0],par[1],par[2],HP,sched=CK.SCHED,K=CK.K_FB,gain_fn=g_,nnu=nnu))[0]
def self_ok_q(B,Lam,b1,cap,HP,g_):
    qc=Lam/(6*B)
    for x in np.geomspace(1e-7,0.05,40):
        q=qc*(1-x)
        if q<0.5: return None
        if min(res_at(b1,B,Lam,q,(B,Lam,b1),HP,g_),res_at(cap,B,Lam,q,(B,Lam,cap),HP,g_))>RES: return q
    return None
def sub0_q(B,Lam,b1,HP,g_):
    B0,L0,h0=HP; qc=L0/(6*B0); bx=(B0-B)/(L0-Lam)
    for x in np.geomspace(1e-7,0.2,60):
        q=qc*(1-x)
        if q<0.5: return None
        if min(res_at(bx,B,Lam,q,HP,HP,g_),res_at(b1,B,Lam,q,HP,HP,g_))>RES: return q
    return None
def feasible(Lam,s,HP,cap,g_):
    B0,L0,h0=HP
    if not Lam<L0: return None
    B=B0-(L0-Lam)*s; bx=s
    if self_ok_q(B,Lam,cap,cap,HP,g_) is None: return None
    # smallest b1 in [bx,cap] with self ok (bisection; self is easier for larger b1)
    if self_ok_q(B,Lam,bx,cap,HP,g_) is not None: return (bx,None,self_ok_q(B,Lam,bx,cap,HP,g_))
    lo,hi=bx,cap
    for _ in range(14):
        mid=(lo+hi)/2
        if self_ok_q(B,Lam,mid,cap,HP,g_) is not None: hi=mid
        else: lo=mid
    q1=sub0_q(B,Lam,hi,HP,g_)
    if q1 is None: return None
    return (hi,q1,self_ok_q(B,Lam,hi,cap,HP,g_))
def solve(HP,s,cap,Lstart):
    g_=CK.gfun(HP,8)
    hi=None
    # coarse scan downward from the old optimum
    for L in [Lstart+0.01, Lstart, Lstart-0.005, Lstart-0.01, Lstart-0.02, Lstart-0.04]:
        if L>=HP[1]: continue
        r=feasible(L,s,HP,cap,g_)
        if r is not None: hi=(L,r)
        else:
            if hi is not None: lo=L; break
    else:
        lo=None
    if hi is None: return None
    if lo is None: lo=hi[0]-0.08
    for _ in range(14):
        mid=(lo+hi[0])/2
        r=feasible(mid,s,HP,cap,g_)
        if r is not None: hi=(mid,r)
        else: lo=mid
    return hi
if __name__=="__main__":
    base=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks', 'cchain_k8b.json')))
    out=sys.argv[1]
    capf=lambda s: min(0.0549989, round(s+0.016,7))
    HP=(1.0,CK.K_FB,0.055)
    nodes=[]; t0=time.time()
    for n in base:
        s=n['pivot']; cap=capf(s)
        Lstart=float(Fr(n['L']))
        sol=solve(HP,s,cap,min(Lstart,HP[1]-1e-6))
        if sol is None:
            print('pivot',s,'infeasible',flush=True); continue
        Lam,info=sol; B=HP[0]-(HP[1]-Lam)*s
        nodes.append(dict(B=B,L=Lam,cap=cap,pivot=s,info=[float(v) if v is not None else None for v in info]))
        HP=(B,Lam,cap)
        print('pivot %.5f B=%.10f L=%.8f (base L %.8f) h@.0423=%.7f h@.0396=%.7f info=%s t=%.0f'%(s,B,Lam,Lstart,B-Lam*0.0423245,B-Lam*0.0396,str(info),time.time()-t0),flush=True)
    json.dump(nodes,open(out,'w'),indent=1)
