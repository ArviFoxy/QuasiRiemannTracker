import sys,time,json
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
DL,P=grids()
base=mk86()
rows=parse_chain()
faces={0:(float(rows[0]['B0']),float(rows[0]['L0']))}
for r in rows: faces[r['i']]=(float(r['B']),float(r['L']))
out=[]
for k in [int(x) for x in sys.argv[1].split(",")]:
    B,L=faces[k]
    r=mkface(B,L,r0=base)
    c,h,s,rr=solve_c_fast(r,iters=20,DL=DL,P=P,hspan=0.03,clo=0.120,chi=0.130)
    cw=rr.check_windows(n=31)
    bad=[(w[0],round(w[1],3),j) for (w,m,j) in cw if m<=0]
    # pointwise (optimistic: use any branch valid at the point)
    cp,hp,sp,rp=solve_c_fast(r,iters=20,DL=DL,P=P,hspan=0.03,clo=0.120,chi=0.130,pointwise=True)
    print('k=%2d  B=%.7f L=%.5f  theta(Sil windows)=%.9f %s | theta(pointwise branches)=%.9f'%(k,B,L,1-c,('BADWIN%d'%len(bad)) if bad else 'ok',1-cp),flush=True)
