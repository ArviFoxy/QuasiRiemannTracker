"""Return-side binding summary for all stored discrete scenarios -> results/diag2_all.json and a compact table."""
import sys, os, json, glob, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import diag2
out = {}
pat = re.compile(r'^e2_g([\d.]+)_f(\d\.\d\d)_b(\d)_d(\d\.\d{3})_dL0.005_q\.json$')
rows = []
for fn in sorted(glob.glob(os.path.join(HERE, 'results', 'e2_g*_dL0.005_q.json'))):
    if not pat.match(os.path.basename(fn)):
        continue
    r = json.load(open(fn))
    try:
        d = diag2.diagnose(r, 'collet')
    except Exception as e:      # noqa
        print(r['name'], 'diag failed', e)
        continue
    nt = d['cover']['newTop']
    out[r['name']] = d
    fb = d.get('fail_box', {})
    rows.append((r['name'], r['theta'], d['ell_needed'], d.get('fail_edge'), None if not fb else (sum(fb['delta']) / 2, sum(fb['p']) / 2),
                 d.get('best_admitted_margin'), nt['by_branch'], nt['tightest'][1], d['box_margins']['small_saving'], d['box_margins']['theta>lo']))
    print('%-40s th=%.9f ell=%.6f fail=%s d*,p*=%s best=%s newTop leaves=%s small_saving=%.4f' % (
        r['name'], r['theta'], d['ell_needed'], d.get('fail_edge'),
        None if not fb else '(%.4f, %.4f)' % (sum(fb['delta']) / 2, sum(fb['p']) / 2),
        d.get('best_admitted_margin') and d['best_admitted_margin'][1], nt['by_branch'], d['box_margins']['small_saving']), flush=True)
json.dump(out, open(os.path.join(HERE, 'results', 'diag2_all.json'), 'w'), indent=1, default=str)
