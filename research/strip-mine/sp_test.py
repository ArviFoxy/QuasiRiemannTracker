"""Our certified faces with the physical window sP varied (mode 'global', slope receipt kept)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import atlas as A
A.init()
for v in sys.argv[1:]:
    P = dict(A.BASE, sP=Fr(v))
    print('sP', v, A.theta_star(P, span=3000), flush=True)
