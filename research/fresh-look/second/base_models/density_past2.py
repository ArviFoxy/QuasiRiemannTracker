"""Faces past Lambda = 2 reached by density-type steps (B traded for Lambda at slope s0), priced in the float model.
Ignores the reference gate (that is the question: what would loosening it buy).  [numerical, float model]"""
import worth as W
base = W.theta_star(5/6)[0]
print('base %.8f' % base)
for s0 in (0.04, 0.06, 0.08, 0.12):
    row = []
    for L in (1.98, 1.95, 1.9, 1.85):
        B = 0.99999 - s0 * (2.005 - L)
        t = W.theta_star(5/6, L=L, B=B, cap=0.134)[0]
        row.append('L %.2f B %.5f: %+.2e' % (L, B, t - base))
    print('s0 %.2f | ' % s0 + ' | '.join(row))
# exchange rates at the end face
dB = 1e-3
tB = W.theta_star(5/6, L=2.005, B=0.99999 - dB, cap=0.134)[0]
tL = W.theta_star(5/6, L=2.005 - 0.01, B=0.99999, cap=0.134)[0]
print('dtheta/dB = %.4f, dtheta/dLambda = %.5f, break-even slope s0* = %.4f' % (-(tB - base) / dB, -(tL - base) / 0.01, ((tL - base) / 0.01) / ((tB - base) / dB)))
