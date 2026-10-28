import sys
sys.path.insert(0,'$SCRATCH/analysis/model')
from common import *

def grids(coarse=(301,201), local=((0.36,0.52),(0.44,0.5),(201,121))):
    dls=np.linspace(0,0.75,coarse[0]); ps=np.linspace(0,0.5,coarse[1])
    DL,P=np.meshgrid(dls,ps,indexing='ij')
    (dlo,dhi),(plo,phi),(nd,npp)=local
    dl2=np.linspace(dlo,dhi,nd); p2=np.linspace(plo,phi,npp)
    DL2,P2=np.meshgrid(dl2,p2,indexing='ij')
    return np.concatenate([DL.ravel(),DL2.ravel()]), np.concatenate([P.ravel(),P2.ravel()])

def env_on(r,DL,P,**kw):
    return r.envelope(DL,P,**kw)

def slack_h(r,DL,P,env,h,c=None):
    """min over grid & edges of theta-res-(Ebase+0.75 d env) for given h (and r.c)"""
    r2=copy.copy(r); r2.h=h
    if c is not None: r2.c=c
    best=1e9; arg=None
    for name,(d,C) in r2.edges().items():
        E=r2.Ebase(d,C,DL,P)+0.75*d*env
        s=r2.theta-r2.reserve-E
        i=int(np.argmin(s))
        if s[i]<best: best=float(s[i]); arg=(name,float(DL[i]),float(P[i]))
    return best,arg

def best_h_fast(r,DL,P,env,hlo,hhi,n=81):
    hs=np.linspace(hlo,hhi,n)
    vals=[slack_h(r,DL,P,env,h)[0] for h in hs]
    i=int(np.argmax(vals))
    # refine
    lo=hs[max(i-1,0)]; hi=hs[min(i+1,n-1)]
    hs2=np.linspace(lo,hi,41)
    vals2=[slack_h(r,DL,P,env,h)[0] for h in hs2]
    j=int(np.argmax(vals2))
    return vals2[j],hs2[j]

def solve_c_fast(r,clo=0.1250,chi=0.1270,iters=40,hspan=0.02,DL=None,P=None,**kw):
    r=copy.deepcopy(r)
    if DL is None: DL,P=grids()
    hg=r.h
    for _ in range(iters):
        cm=0.5*(clo+chi); r.c=cm
        env=env_on(r,DL,P,**kw)
        s,h=best_h_fast(r,DL,P,env,hg-hspan,hg+hspan)
        if s>=0: clo=cm; hg=h
        else: chi=cm
    r.c=clo; env=env_on(r,DL,P,**kw)
    s,h=best_h_fast(r,DL,P,env,hg-hspan/4,hg+hspan/4)
    r.h=h
    return clo,h,s,r
