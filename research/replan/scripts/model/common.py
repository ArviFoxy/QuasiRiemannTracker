import sys
sys.path.insert(0,'$SCRATCH/analysis/model')
from retmodel import *
from gates import *
from fractions import Fraction as Fr
import numpy as np, copy
NORM='$SCRATCH/analysis/norm'
def F(s): return float(Fr(s))

def mk86(**over):
    r=Ret(c=F('630221/5000000'),h=F('8051/10000'),
        faces={'C':Face(F('9888151/10000000'),F('4683001/2000000'),F('9999/100000'),False),'capP':Face(F('9888151/10000000'),F('4683001/2000000'),F('31/500'),True)},
        physB=F('9888151/10000000'),physL=F('4683001/2000000'),mMinus=F('377/1000'),windows=parse_windows(NORM+'/pr86/Return/Windows.lean'))
    for k,v in over.items(): setattr(r,k,v)
    return r

def mkface(B,L,r0=None,capC=0.09999,capP=0.062,mMinus=None,windows=None,**over):
    r0=r0 or mk86()
    r=copy.deepcopy(r0)
    r.faces={'C':Face(B,L,capC,False),'capP':Face(B,L,capP,True)}
    r.physB=B; r.physL=L
    if mMinus is not None: r.mMinus=mMinus
    if windows is not None: r.windows=windows
    for k,v in over.items(): setattr(r,k,v)
    return r

def slack(r,nd=601,npp=401,**kw):
    return r.min_margin(nd=nd,npp=npp,**kw)[0]

def best_h(r,hs=None,nd=601,npp=401):
    hs=hs if hs is not None else np.linspace(r.h-0.01,r.h+0.01,41)
    best=(-1e9,None)
    for h in hs:
        r.h=h
        s=slack(r,nd,npp)
        if s>best[0]: best=(s,h)
    return best

def solve_c(r, clo=0.1255, chi=0.1265, iters=30, nd=601, npp=401, hspan=0.01, nh=41, hguess=None):
    """largest c such that max_h slack >= 0 (slack monotone decreasing in c)"""
    r=copy.deepcopy(r)
    hg=hguess if hguess is not None else r.h
    for _ in range(iters):
        cm=0.5*(clo+chi)
        r.c=cm
        s,h=best_h(r,np.linspace(hg-hspan,hg+hspan,nh),nd,npp)
        if s>=0: clo=cm; hg=h
        else: chi=cm
    r.c=clo
    s,h=best_h(r,np.linspace(hg-hspan/4,hg+hspan/4,41),nd,npp)
    r.h=h
    return clo,h,r
