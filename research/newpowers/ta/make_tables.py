"""Markdown tables for the report from results/*.json"""
import glob, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
TARGET = 0.8739058
VARS = ['pr83', 'a', 'c', 'b0', 'b1', 'd1', 'd2', 'd3', 'd4', 'cu', 'u']
NAMES = {'pr83': 'PR 83 (unmarked rho, reference)', 'a': '(a) black box, dummies to 7/37', 'c': '(c) face-based count, diluted',
         'b0': '(b) limited supply = s0, full width (B2 markedcount)', 'b1': '(b+) limited supply, partial z (= Lemma A_1, natural plain face)',
         'd1': '(d) K=1, parent plain face', 'd2': '(d) K=2', 'd3': '(d) K=3', 'd4': '(d) K=4',
         'cu': '(c-u) face-based undiluted (= K=inf)', 'u': 'ideal rowCount, undiluted (= K=inf, natural plain face)'}
PAT = re.compile(r'^(ode_)?([a-z0-9]+)_f(\d\.\d\d)_b(\d)_d(\d\.\d{3})(_dL([\d.e-]+))?$')


def load():
    res = {}
    for fn in glob.glob(os.path.join(HERE, 'results', 'eval_*.json')):
        r = json.load(open(fn))
        m = PAT.match(r.get('name', ''))
        if not m:
            continue
        ode, var, fl, boot, dfac, _, dL = m.groups()
        key = ('ode' if ode else 'dL' + dL, var, float(fl), int(boot), float(dfac))
        res[key] = r
    return res


def cell(r, ode=False):
    if r is None:
        return '-'
    return '%.7f (%+.1f)' % (r['theta'], 1e6 * (r['theta'] - TARGET))


def table(res, mode, setting, floors=(0.60, 0.55, 0.50), vars_=VARS):
    out = ['| variant | ' + ' | '.join('floor %.2f' % f for f in floors) + ' |', '|---|' + '---|' * len(floors)]
    for v in vars_:
        cells = [cell(res.get((mode, v, f) + setting)) for f in floors]
        if all(c == '-' for c in cells):
            continue
        out.append('| %s | %s |' % (NAMES[v], ' | '.join(cells)))
    return '\n'.join(out)


if __name__ == '__main__':
    res = load()
    for mode, mname in (('ode', 'ODE limit (family theorem, Delta L -> 0)'), ('dL0.005', 'explicit chain Delta L = 0.005')):
        for setting, sname in (((0, 0.999), 'base (no bootstrap, 0.999)'), ((1, 1.0), 'all-on (bootstrap kappa = 2*theta_rec-1, 0.999 -> 1)')):
            print('**%s, %s**: theta* and gap to 0.8739058 in 1e-6\n' % (mname, sname))
            print(table(res, mode, setting))
            print()
