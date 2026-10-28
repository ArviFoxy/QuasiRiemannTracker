"""Markdown tables from results/e2_*.json (second-generation runs)."""
import glob, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
BAR = 0.8739058
PAT_D = re.compile(r'^g([\d.]+)_f(\d\.\d\d)_b(\d)_d(\d\.\d{3})_dL([\d.e-]+)_(q|range)(.*)$')
PAT_O = re.compile(r'^ode2_g([\d.]+)_f(\d\.\d\d)_b(\d)_d(\d\.\d{3})(.*)$')


def load():
    res = {}
    for fn in glob.glob(os.path.join(HERE, 'results', 'e2_*.json')):
        r = json.load(open(fn))
        nm = r.get('name', '')
        m = PAT_D.match(nm)
        if m:
            g, f, b, d, dL, mode, rest = m.groups()
            if rest:
                continue
            res[('disc', float(g), float(f), int(b), float(d))] = r
            continue
        m = PAT_O.match(nm)
        if m:
            g, f, b, d, rest = m.groups()
            if rest:
                continue
            res[('ode', float(g), float(f), int(b), float(d))] = r
    return res


def cell(r):
    if r is None:
        return '-'
    return '%.7f (%+.1f)' % (r['theta'], 1e6 * (r['theta'] - BAR))


def table(res, mode, gain, floors=(0.60, 0.55, 0.50)):
    sets = [('base (no boot, 0.999)', 0, 0.999), ('+ bootstrap', 1, 0.999), ('+ 0.999->1', 0, 1.0), ('all-on', 1, 1.0)]
    out = ['| setting | ' + ' | '.join('floor %.2f' % f for f in floors) + ' |', '|---|' + '---|' * len(floors)]
    for nm, b, d in sets:
        out.append('| %s | %s |' % (nm, ' | '.join(cell(res.get((mode, gain, f, b, d))) for f in floors)))
    return '\n'.join(out)


def faces_table(res, mode, gain, floors=(0.60, 0.55, 0.50)):
    out = ['| floor | setting | theta* | count face (L_C, B_C, s0) | physical face (L_P, B_P) | h | ell needed |', '|---|---|---|---|---|---|---|']
    for f in floors:
        for nm, b, d in (('base', 0, 0.999), ('all-on', 1, 1.0)):
            r = res.get((mode, gain, f, b, d))
            if r is None:
                continue
            out.append('| %.2f | %s | %.9f | %.4f, %.6f, %.4f | %.4f, %.6f | %.6f | %.5f |' % (
                f, nm, r['theta'], r['C']['L'], r['C']['B'], r['C']['s0'], r['P']['L'], r['P']['B'], r['h'], 11 / 3 - 4 * r['theta']))
    return '\n'.join(out)


if __name__ == '__main__':
    res = load()
    for mode, mname in (('disc', 'explicit chain, Delta L = 0.005'), ('ode', 'ODE limit (Delta L -> 0)')):
        for gain, gname in ((1.0, 'marked gate (Lean gainC, K = 8)'), (0.0, 'PR 83 gate (gain off)')):
            if not any(k[0] == mode and k[1] == gain for k in res):
                continue
            print('**%s, %s**  theta* (gap to 0.8739058 in 1e-6)\n' % (mname, gname))
            print(table(res, mode, gain))
            print()
            print(faces_table(res, mode, gain))
            print()
