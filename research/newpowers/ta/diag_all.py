"""Binding diagnostics (failing edge/box, admitted-branch margins, BoundsN margins) for result files -> results/diag_*.json"""
import sys, os, json, glob
import exact
HERE = os.path.dirname(os.path.abspath(__file__))
pats = sys.argv[1:] or ['results/eval_ode_*_b1_d1.000.json']
out = {}
for pat in pats:
    for fn in sorted(glob.glob(os.path.join(HERE, pat))):
        r = json.load(open(fn))
        if '_lev' in fn or '_dR' in fn or '_win' in fn or '_sig' in fn or '_scan' in fn or '_hypo' in fn:
            continue
        try:
            d = exact.diagnose(r['C']['B'], r['C']['L'], r['P']['B'], r['P']['L'], r['theta_units'])
        except Exception as e:     # noqa
            d = {'error': str(e)}
        out[r['name']] = dict(theta=r['theta'], C=r['C'], P=r['P'], diag=d)
        fb = d.get('fail_box', {})
        print('%-34s theta=%.9f h=%.5f ell=%.5f y=%.4f | fail %s delta*=%s p*=%s | best admitted %s' % (
            r['name'], r['theta'], d.get('h', 0), d.get('ell', 0), d.get('y', 0), d.get('below'),
            None if not fb else '%.4f' % (sum(fb['delta']) / 2), None if not fb else '%.4f' % (sum(fb['p']) / 2), d.get('best_admitted_margin')), flush=True)
json.dump(out, open(os.path.join(HERE, 'results', 'diag_%s.json' % ('main' if len(sys.argv) < 2 else 'custom')), 'w'), indent=1, default=str)
