"""Hybrid cap induction (Lemma F) chain with q floor QF, fine pivots after S1, ending at SEND.
usage: python3 hybchain2.py QF S1 STEP2 SEND OUT.json"""
import sys, os, json, time, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cchain_k as CK
import hybchain as H
QF=float(sys.argv[1]); S1=float(sys.argv[2]); STEP2=float(sys.argv[3]); SEND=float(sys.argv[4]); out=sys.argv[5]
def self_ok_q(B,Lam,b1,cap,HP,g_):
    qc=Lam/(6*B)
    for x in np.geomspace(1e-7,0.05,40):
        q=qc*(1-x)
        if q<QF: return None
        if min(H.res_at(b1,B,Lam,q,(B,Lam,b1),HP,g_),H.res_at(cap,B,Lam,q,(B,Lam,cap),HP,g_))>H.RES: return q
    return None
def sub0_q(B,Lam,b1,HP,g_):
    B0,L0,h0=HP; qc=L0/(6*B0); bx=(B0-B)/(L0-Lam)
    for x in np.geomspace(1e-7,0.2,60):
        q=qc*(1-x)
        if q<QF: return None
        if min(H.res_at(bx,B,Lam,q,HP,HP,g_),H.res_at(b1,B,Lam,q,HP,HP,g_))>H.RES: return q
    return None
H.self_ok_q=self_ok_q; H.sub0_q=sub0_q
piv=[round(0.0135+0.0005*i,5) for i in range(int(round((S1-0.0135)/0.0005))+1)]
s=piv[-1]
while s < SEND-1e-9:
    s=round(s+STEP2,6); piv.append(s)
capf=lambda s: min(0.0549989, round(s+0.016,7))
HP=(1.0,CK.K_FB,0.055); nodes=[]; t0=time.time()
for s in piv:
    cap=capf(s)
    sol=H.solve(HP,s,cap,HP[1]-0.004)
    if sol is None:
        print('pivot',s,'infeasible',flush=True); continue
    Lam,info=sol; B=HP[0]-(HP[1]-Lam)*s
    nodes.append(dict(B=B,L=Lam,cap=cap,pivot=s,info=[float(v) if v is not None else None for v in info]))
    HP=(B,Lam,cap)
    print('pivot %.5f B=%.10f L=%.8f h@.045=%.7f h@.0412=%.7f q2=%s t=%.0f'%(s,B,Lam,B-Lam*0.045,B-Lam*0.0412,str(info[2]),time.time()-t0),flush=True)
    json.dump(nodes,open(out,'w'),indent=1)
