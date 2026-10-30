# E(delta) landscape at the #97 binding theta (newTop row), p=1/2, Collet NR2 count
import numpy as np
def count(d, p=0.5, B=0.99999, L=2.005, LONG=5/6):
    V = LONG - d; D = 3 - p - 4*p/L; A = 2 - 4*p/L; C0 = 1 - 2*B*p/L; U = (1-p)*C0
    J = V*D + d*(1-p)*A; N = (1-d)*J + V*d*U
    return N/J
th = 0.87341197; h = 0.8001361; B=0.99999; L=2.005; numCap=0.075
c = 1-th; ell = 4*c-1/3; y = h-2*ell; C = min(numCap*h, (2*y-(2-B)*h)/L)
for d in np.arange(0.30, 0.76, 0.025):
    R = count(d); E = 0.5+13*h/75-y/2-ell/2-0.09*h+d/2+d*0.5*(ell-C/2)+0.75*h*R
    print('delta %.3f  R %.4f  DH %.4f  E-theta %+.5f' % (d, R, 1-d, E-th))
