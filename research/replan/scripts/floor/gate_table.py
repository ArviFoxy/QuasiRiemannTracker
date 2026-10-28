import sys, re
sys.path.insert(0,'.')
from floor_chain import *
def parse(fn):
    rows=[]
    prev=(0.9888151,2.3415)
    for l in open(fn):
        m=re.match(r'k=\s*(\d+) L=([0-9.]+) B=([0-9.]+) s0=([0-9.]+) A=([0-9.]+) D=([0-9.]+)',l)
        if m:
            k,L,B,s0,A,D=int(m.group(1)),*(float(m.group(i)) for i in range(2,7))
            rows.append(dict(k=k,L=L,B=B,s0=s0,A=A,D=D,B0=prev[0],L0=prev[1])); prev=(B,L)
    return rows
for fn,ks in (('chain_floor_0.60.log',(1,14,27,28)),('chain_floor_-1.0.log',(1,14,28,44))):
    rows=parse(fn)
    for r in rows:
        if r['k'] in ks:
            # use exact slope s0 -> B = B0 - s0*dL to avoid rounding
            B=r['B0']-r['s0']*(r['L0']-r['L'])
            m,s0,vmax=gmin(r['B0'],r['L0'],0.1,B,r['L'],0.1,r['A'],r['D'],floor=0.60 if '0.60' in fn else -1.0,N=1500)
            print(fn,'k=%d L=%.4f s0=%.5f vmax=%.4f'%(r['k'],r['L'],s0,vmax))
            print('   '+'  '.join('%s=%.3g'%(g,m[g]) for g in GATES))
