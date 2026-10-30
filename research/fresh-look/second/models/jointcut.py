# Does the flat E(delta) near 1/2 survive if PR 93's joint count J(nu,delta)=3(1-d)(1-nu)/(3-nu-2d)
# (valid for slot slope nu = 2 p delta > 1/2) is added?  Then price sub-sqrt (delta<1/2) count gains. [numerical]
import sys, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from pclass import theta_star, DD, PP
nu = 2*PP*DD
J = 3*(1-DD)*(1-nu)/(3-nu-2*DD)
withJ = lambda e: np.where(nu > 0.5, np.minimum(e, J), e)
b0 = theta_star(); bJ = theta_star(withJ)
print('base %.8f (d %.3f) ; with PR93 joint count for 2p*delta>1/2: %.8f (d %.3f p %.3f) dtheta %+.2e' % (b0[0], b0[1], bJ[0], bJ[1], bJ[2], bJ[0]-b0[0]))
for dR in (0.0024, 0.005, 0.01, 0.03):
    f = lambda e, dR=dR: withJ(np.where(DD < 0.5, e - dR, e))
    t = theta_star(f)
    print('with J, count -%.4f on delta<1/2: theta %.8f dtheta(vs base) %+.2e bind d %.3f p %.3f' % (dR, t[0], t[0]-b0[0], t[1], t[2]))
