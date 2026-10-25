"""Exact (Fraction) check of SourceValid2 at sample nodes of family v2, with lean_certs.check_node."""
import sys, os, random
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import lean_certs as LC
import family2 as F2
import polyq as P

def node_at(fam, j, y):
    B, L, B0, L0, sv = fam.polys(j)
    q = (1 - fam.den)*P.ev(L0, y)/(6*P.ev(B0, y))
    return dict(B=P.ev(B, y), L=P.ev(L, y), cap=F2.CAPMAX, q=q, allowance=F2.FEES[0], lowFee=F2.FEES[1], highFee=F2.FEES[2])

def parent_at(fam, j, y):
    B, L, B0, L0, sv = fam.polys(j)
    return dict(B=P.ev(B0, y), L=P.ev(L0, y), cap=F2.CAPMAX, q=Fr(0), allowance=F2.FEES[0], lowFee=F2.FEES[1], highFee=F2.FEES[2])

if __name__ == "__main__":
    sig = [float(x) for x in sys.argv[1].split(',')]
    fam, _ = F2.build2(sig, m=16)
    Dy = fam.Dy
    random.seed(0)
    bad = 0
    for j in range(len(fam.H)):
        ys = [Dy, 2*Dy, Fr(1, 2), 1 - Dy] + [Fr(random.randrange(1, 2**16 - 1), 2**16) for _ in range(6)]
        for y in ys:
            n = node_at(fam, j, y); low = parent_at(fam, j, y)
            ok, msgs, trees = LC.check_node(n, low, low, Fr(8))
            cr = LC.crossing(n, low)
            # CellRatio
            cell = all(2*(b - 2*n['allowance']) <= LC.sourceF(n, low, b) - n['allowance'] for b in (cr, n['cap']))
            if not (ok and cell):
                bad += 1
                print(f"piece {j} y={float(y):.6f}: FAIL {msgs[:3]} cell={cell}", flush=True)
        print(f"piece {j}: checked {len(ys)} nodes; s range {float(fam.sig[j]):.6f}..{float(fam.sig[j+1]):.6f}", flush=True)
    print("ALL OK" if bad == 0 else f"{bad} failures")
