"""E5. theta* of the merged return when the region is the K = 1/2 + 1e-3 native line (selected-norm leaf).
Global check (all edges, delta, p, guards) with candidate count faces from the line; physical face = the line's
face of largest physical capacity.  [numerical]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'face-region', 'value'))
from native_line import run
from globalcheck import theta_global

L_end, c_end, reason, path = run(0.5 + 1e-3)
B = 0.99999
y2, dp = 2 * 69313573 / 150000000, 0.8044451001
best_phys = max(path, key=lambda p: (y2 - (2 - B) * dp) / p[0])
PF = (B, best_phys[0])
print('physical face: (%.5f, %.5f)' % PF, flush=True)
for Lq in (2.2, 2.1, 2.05, 2.02, L_end):
    pt = min(path, key=lambda p: abs(p[0] - Lq))
    L, c = pt[0], pt[1]
    t, where = theta_global((B, L, min(c, 0.1499)), PF)
    print('count face (%.5f, %.5f, cap %.4f): global theta* = %.8f  %+.2e  binding %s d=%.2f p=%.2f %s'
          % ((B, L, c, t, t - 0.87387234) + where), flush=True)
