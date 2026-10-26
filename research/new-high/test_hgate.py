import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'faceless-chain'))
sys.path.insert(0, os.path.join(HERE, '..', 'mixed-step'))
sys.argv = ['x', '/dev/null', '6']
import continuum_mixed as CM
G = CM.G
import numpy as np
import hgate as HG
s = 0.057; E = 0.8443438737661075; L = 2.1293403859968656; q = 0.581
B = E + L*s
n = G.node(B, L, 0.075, q, G.FINE)
for b in (s, 0.075):
    nu = np.linspace(q, 0.75, 21); p = np.linspace(0, 0.5, 41)
    orig = G.high_gate(n, n, n, b, nu, p)
    gen = HG.high_gate_gen(n, n, n, b, nu, p, basics=G.basics)
    print('b', b, 'orig min', orig.min(), 'gen min', gen.min(), 'maxdiff', np.abs(orig.min(0) - gen[0]).max())
    k = np.unravel_index(orig.argmin(), orig.shape); print('argmin branch,nu,p', k[0], nu[k[1]], p[k[2]])
    print(G.margins(n, n, n, b))
