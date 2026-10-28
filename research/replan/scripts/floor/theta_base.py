import sys
sys.path.insert(0,'.')
from theta_floor import *
for tag,fc in (('PR86 end face (L=2.3415)',(0.9888151,2.3415)),):
    th,bad=theta(fc,PFACE); ths,_=theta(fc,fc)
    print(tag,'role split (P=step40 face) theta=%.9f bad=%s | single=%.9f'%(th,bad,ths),flush=True)
