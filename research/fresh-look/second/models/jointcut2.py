# Sub-sqrt improvement measured in slot slope nu = 2 p delta (the sqrt barrier of selected norms / joint count),
# together with PR 93's joint count for nu > 1/2. [numerical]
import sys, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from pclass import theta_star, DD, PP
nu = 2*PP*DD
J = 3*(1-DD)*(1-nu)/(3-nu-2*DD)
withJ = lambda e: np.where(nu > 0.5, np.minimum(e, J), e)
b0 = theta_star()
for dR in (0.0024, 0.005, 0.01):
    f = lambda e, dR=dR: withJ(np.where(nu <= 0.5, e - dR, e))
    t = theta_star(f); print('with J, count -%.4f where nu<=1/2: dtheta %+.2e bind d %.3f p %.3f' % (dR, t[0]-b0[0], t[1], t[2]))
    g = lambda e, dR=dR: np.where(nu <= 0.5, e - dR, e)
    t = theta_star(g); print('   no J,  count -%.4f where nu<=1/2: dtheta %+.2e bind d %.3f p %.3f' % (dR, t[0]-b0[0], t[1], t[2]))
# extending the joint count below 1/2: J valid for nu > nu0 (a sub-sqrt joint count)
for nu0 in (0.49, 0.48, 0.46, 0.45):
    f = lambda e, nu0=nu0: np.where(nu > nu0, np.minimum(e, J), e)
    t = theta_star(f); print('joint count J valid for nu > %.2f: dtheta %+.2e bind d %.3f p %.3f' % (nu0, t[0]-b0[0], t[1], t[2]))
