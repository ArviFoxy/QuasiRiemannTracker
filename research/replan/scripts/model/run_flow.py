import sys,time,json
sys.path.insert(0,'$SCRATCH/analysis/model')
from flow import *
dL=float(sys.argv[1]); eps=float(sys.argv[2]) if len(sys.argv)>2 else 1e-6
Lend=float(sys.argv[3]) if len(sys.argv)>3 else 2.30
out=open(f'$SCRATCH/analysis/model/flow_dL{dL}_eps{eps}.jsonl','w')
B0,L0,c0=0.99999,2.5715,0.1397
c=0.1
guess=(np.log(0.6065),np.log(400.0))
k=0
t0=time.time()
while True:
    L=L0-dL
    if L<Lend: break
    s,A,D=best_step(B0,L0,c0,dL,c,eps=eps,guess=guess,N=300)
    if s>=0.9:   # infeasible
        out.write(json.dumps(dict(k=k+1,infeasible=True,B0=B0,L0=L0))+'\n'); out.flush(); break
    B=B0-s*dL
    k+=1
    out.write(json.dumps(dict(k=k,B0=B0,L0=L0,B=B,L=L,s0=s,A=A,D=D,t=time.time()-t0))+'\n'); out.flush()
    guess=(np.log(A),np.log(D))
    B0,L0,c0=B,L,c
