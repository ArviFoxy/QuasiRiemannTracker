import json, sys
from fractions import Fraction as Fr
import theta_eval as T
rows = json.load(open(sys.argv[1]))
CAP = Fr(549989, 10**7)
F = lambda r: (Fr(r['B']).limit_denominator(10**13), Fr(r['L']).limit_denominator(10**13), CAP)
rows = [r for r in rows if r['B'] >= 22/23 - 1e-12]
Cs = [r for r in rows if r['s'] >= 0.0412][::2][-5:]
Ps = [r for r in rows if 0.0384 <= r['s'] <= 0.0412][::3]
best = None
for c in Cs[-2:]:
    for p in Ps:
        th = T.theta_star(F(c), F(p))
        print(f"C s={c['s']:.5f} P s={p['s']:.5f}: theta*={th}", flush=True)
        if th and (best is None or th < best[0]): best = (th, c['s'], p['s'])
print("best", best)
