exec(open('fastopt.py').read().split("for cap in")[0])
from fractions import Fraction as F
th=437423/500000
print('hcap',hcap(th))
for h in np.linspace(.7946,.79523,22):
    print('%.6f %.3e %.3e'%(h,margin(th,h,True),margin(th,h,False)))
# exact checks for candidate rational h
LAMq=F(19312,4787); Bq=F(1419985639,1436100000)
thq=F(437423,500000); ellq=F(11,3)-4*thq
for hq in (F(795,1000),F(7951,10000),F(79515,100000),F(7952,10000),F(79505,100000)):
    y=hq-2*ellq; dm=hq-F(1,1000); dp=hq+F(1,10**10); t0=F(1,1000)
    nmin=1-y/dm; zmax=(Bq-2*nmin)/LAMq; bmax=2*y/dm-1
    nmax=1-y/dp+t0; zmin=(Bq-2*nmax)/LAMq
    print(hq, float(hq),'slotgap',float(F(37,1000)-zmax),'bmaxgap',float(F(4,25)-bmax),'plaingap',float(F(264,625)-nmax),'slotlo',float(zmin-F(17,500)),'margin',margin(th,float(hq)))
