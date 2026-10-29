"""make_table.py -- Q4 table from scan_split.py outputs (scan_k*.json)."""
import json, glob, os
HERE = os.path.dirname(os.path.abspath(__file__))
rows = []
for fn in sorted(glob.glob(os.path.join(HERE, 'scan_k*.json'))):
    o = json.load(open(fn))
    rows.append(o)
base = [o for o in rows if o['kappa'] >= 0.5716 and o['kroom'] == 0]
b = base[0]['theta'] if base else None
print('| scale kappa | room kappa\' | twisted region (q=3/4) | count face (L, B) | physical face (L, B) | theta (ODE) | dtheta vs base |')
print('|---|---|---|---|---|---|---|')
for o in sorted(rows, key=lambda o: (o['kroom'], o['kappa'])):
    reg = 'none' if o['Lswitch'] >= 2.5714 else 'L in [%.4f, 2.5715]' % o['Lswitch']
    d = '' if b is None else '%+.2e' % (o['theta'] - b)
    print('| %.3f | %.4f | %s | (%.4f, %.5f) | (%.4f, %.5f) | %.9f | %s |' % (
        o['kappa'], o['kroom'], reg, o['C']['L'], o['C']['B'], o['P']['L'], o['P']['B'], o['theta'], d))
