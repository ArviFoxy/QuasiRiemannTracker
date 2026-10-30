"""Which guard makes each branch inadmissible near the binding points of the E5 retune design (newTop, p = 1/2)."""
import numpy as np
from fast import guards, old_count
from model import hceiling
from fractions import Fraction as Fr
NAMES = ['D>0','A>0','C0>0','J>0','t>1','t<1.2499','r>23/37','r<1','m>lowerM','m<upperM','tail','antitone','11/25>nM','widths','cap>sM']
cB, cL, cCap, w = 3913/4000, 101/50, 21/200, 22/625
faces = {'C': (cB, cL, cCap, False), 'capC': (cB, cL, cCap, True), 'weakC7': (cB-w, cL, cCap, False), 'capP': (0.99999, 2.02, 0.1097, True)}
for p in (0.5, 0.45, 0.4):
  print('p =', p)
  for d in np.arange(0.40, 0.60, 0.01):
    row = []
    for nm, (B, L, cap, capped) in faces.items():
        g, b = guards(d, p, B, L, cap, capped)
        bad = [NAMES[i] for i in range(15) if np.asarray(g[i]) <= 0]
        cnt = b['N']/b['J']
        row.append('%s:%.4f%s' % (nm, cnt, '' if not bad else '[' + ','.join(bad) + ']'))
    kappa = 1 - 2*(1-0.87350266)
    print('  d=%.3f old=%.4f ' % (d, old_count(d, p, kappa)) + '  '.join(row))
