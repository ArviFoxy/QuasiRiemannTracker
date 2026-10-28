"""Aggregate results/eval_*.json into markdown tables."""
import glob, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
TARGET = 0.8739058
RECORD = 0.8739558
VARS = ['pr83', 'a', 'c', 'b0', 'b1', 'd1', 'd2', 'd3', 'd4', 'cu', 'u']
NAMES = {'pr83': 'PR 83 gate (unmarked)', 'a': '(a) black box (dummies to 7/37)', 'c': '(c) face-based count, diluted',
         'b0': '(b) limited supply s0, full width (B2)', 'b1': '(b+) limited supply, partial z',
         'd1': '(d) K=1', 'd2': '(d) K=2', 'd3': '(d) K=3', 'd4': '(d) K=4',
         'cu': '(c-u) face-based, undiluted (= K=inf)', 'u': 'ideal rowCount, undiluted (B2 "idealised")'}


def load(pattern):
    out = {}
    import re
    pat = re.compile(r'^(ode_)?[a-z0-9]+_f\d\.\d\d_b\d_d\d\.\d{3}(_dL[\d.e-]+)?$')
    for fn in glob.glob(os.path.join(HERE, 'results', pattern)):
        r = json.load(open(fn))
        if not pat.match(r.get('name', '')):
            continue
        out[(r['var'], round(r['floor'], 2), int(r['boot']), round(r['dfac'], 3))] = r
    return out


def table(res, title, setting, floors=(0.60, 0.55, 0.50), fmt='%.7f'):
    lines = [title, '', '| variant | ' + ' | '.join('floor %.2f' % f for f in floors) + ' |', '|---|' + '---|' * len(floors)]
    for v in VARS:
        cells = []
        for f in floors:
            r = res.get((v, f) + setting)
            if r is None:
                cells.append('-')
            else:
                cells.append(('%s (%+.1f)' % (fmt % r['theta'], 1e6 * (r['theta'] - TARGET))))
        lines.append('| %s | %s |' % (NAMES[v], ' | '.join(cells)))
    return '\n'.join(lines)


if __name__ == '__main__':
    ode = load('eval_ode_*.json')
    disc = load('eval_*_dL0.005.json')
    for name, res in (('ODE limit', ode), ('discrete dL=0.005', disc)):
        for setting, sname in (((0, 0.999), 'base: no bootstrap, 0.999'), ((1, 1.0), 'all-on: bootstrap + 0.999->1')):
            print(table(res, '**%s, %s**  (theta*, gap to 0.8739058 in 1e-6)' % (name, sname), setting))
            print()
