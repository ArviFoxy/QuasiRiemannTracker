import sys, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from pclass import theta_star, DD, PP
nu = 2*PP*DD
J = 3*(1-DD)*(1-nu)/(3-nu-2*DD)
b0 = theta_star()
for nu0 in (0.42, 0.40, 0.38, 0.36, 0.33, 0.30, 0.25):
    f = lambda e, nu0=nu0: np.where(nu > nu0, np.minimum(e, J), e)
    t = theta_star(f); print('joint count (DH-strength) valid for nu > %.2f: dtheta %+.2e bind d %.3f p %.3f' % (nu0, t[0]-b0[0], t[1], t[2]), flush=True)
