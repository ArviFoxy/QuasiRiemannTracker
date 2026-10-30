# Value of a count improvement restricted to a delta-range (e.g. below the sqrt-barrier delta < 1/2,
# or only where 2*p*delta < 1/2).  Float model of the newTop row (worth.py machinery). [numerical]
import sys, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from pclass import theta_star, DD, PP
b = theta_star()
print('base %.8f bind d %.3f p %.3f' % (b[0], b[1], b[2]))
for lo, hi in ((0.30, 0.50), (0.40, 0.50), (0.42, 0.48), (0.44, 0.47), (0.30, 0.65)):
    for dR in (0.0024, 0.01, 0.03):
        f = lambda e, lo=lo, hi=hi, dR=dR: np.where((DD >= lo) & (DD < hi), e - dR, e)
        t = theta_star(f)
        print('delta in [%.2f,%.2f) count -%.4f: theta %.8f dtheta %+.2e bind d %.3f p %.3f' % (lo, hi, dR, t[0], t[0]-b[0], t[1], t[2]))
