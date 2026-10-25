import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import lean_certs as LC
import family2 as F2
import polyq as P
from exact_check import node_at

def node_raw(fam, j, y):
    B, L, B0, L0, sv = fam.polys(j)
    return dict(B=P.ev(B, y), L=P.ev(L, y), cap=F2.CAPMAX, q=Fr(0), allowance=F2.FEES[0], lowFee=F2.FEES[1], highFee=F2.FEES[2])

sig = [float(x) for x in sys.argv[1].split(',')]
fam, _ = F2.build2(sig, m=16)
Dy = fam.Dy
# first step: parent natural
nat = dict(B=Fr(1), L=F2.K, cap=Fr(11, 200), q=Fr(0), allowance=Fr(1, 10**12), lowFee=Fr(1, 10**8), highFee=Fr(1, 10**7))
n0 = node_at(fam, 0, Fr(0))
ok, msgs, trees = LC.check_node(n0, nat, nat, Fr(8)); cr = LC.crossing(n0, nat)
print("first step:", ok, msgs[:4], "crossing", float(cr), "q", float(n0['q']), "den", float(LC.sourceDen(n0, nat)))
for j in range(1, len(fam.H)):
    child = node_at(fam, j, Fr(0))
    par = node_raw(fam, j - 1, 1 - Dy)
    ok, msgs, trees = LC.check_node(child, par, par, Fr(8))
    cr = LC.crossing(child, par)
    cell = all(2*(b - 2*child['allowance']) <= LC.sourceF(child, par, b) - child['allowance'] for b in (cr, child['cap']))
    print(f"junction {j}: ok={ok} cell={cell} {msgs[:3]} crossing {float(cr):.9f} vs sig {float(fam.sig[j]):.9f} den {float(LC.sourceDen(child, par)):.3e}")
