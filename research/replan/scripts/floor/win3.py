import sys, copy
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
DL,P=grids()
base=mk86()
PF=(0.9907142,2.3715)
for tag,fc in (('PR86 end (current)',(0.9888151,2.3415)),('floor-0.64 step6',(0.986731,2.3115)),('floor-0.62 step16',(0.983137,2.2615)),('floor-0.60 step27',(0.978722,2.2065))):
    r=copy.deepcopy(base)
    r.faces={'C':Face(fc[0],fc[1],0.09999,False),'capP':Face(PF[0],PF[1],0.062,True)}
    r.physB,r.physL=PF
    c,h,s,rr=solve_c_fast(r,iters=16,DL=DL,P=P,hspan=0.03,clo=0.12,chi=0.13)
    cw=rr.check_windows(n=41)
    out=[]
    for i,(w,m,j) in enumerate(cw):
        if m<=0.003: out.append('win%02d %s margin=%.4g guard=%s'%(i+1,w,m,j))
    print(tag,'theta=%.9f'%(1-c)); 
    for o in out: print('   ',o)
