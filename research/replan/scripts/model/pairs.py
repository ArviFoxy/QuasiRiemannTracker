import sys,time,json
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
DL,P=grids()
base=mk86()
rows=parse_chain()
faces={0:(float(rows[0]['B0']),float(rows[0]['L0']))}
for r in rows: faces[r['i']]=(float(r['B']),float(r['L']))
def theta(jc,kp):
    r=copy.deepcopy(base)
    Bc,Lc=faces[jc]; Bp,Lp=faces[kp]
    r.faces={'C':Face(Bc,Lc,0.09999,False),'capP':Face(Bp,Lp,0.062,True)}
    r.physB=Bp; r.physL=Lp
    c,h,s,rr=solve_c_fast(r,iters=20,DL=DL,P=P,hspan=0.02)
    cw=rr.check_windows(n=31)
    bad=[(w[0],round(w[1],3),j) for (w,m,j) in cw if m<=0]
    return 1-c,h,bad
if __name__=='__main__':
    for jc,kp in [(46,46),(46,44),(46,42),(46,40),(46,38),(46,36),(46,34),(44,40),(45,41),(42,40)]:
        th,h,bad=theta(jc,kp)
        print('count-face step %d, physical-face step %d -> theta=%.9f h=%.4f bad=%s'%(jc,kp,th,h,bad),flush=True)
