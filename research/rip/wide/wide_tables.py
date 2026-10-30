"""Markdown tables for FRESH_LOOK.md from the wide_B*_s*.json files written by wide_tests.py.
Run: python3 -I wide_tables.py [json ...]   (default: every wide_B*_s*.json in this directory)."""
import sys, os, json, glob, math
HERE = os.path.dirname(os.path.abspath(__file__))
files = sys.argv[1:] or sorted(glob.glob(os.path.join(HERE, 'wide_B*_s*.json')))
runs = []
for fn in files:
    with open(fn) as fh: d = json.load(fh)
    for rho, r in d['rho'].items():
        runs.append((d, float(rho), r))
runs.sort(key=lambda t: (t[0]['B'], t[0]['L'], t[0]['P0'], -t[1]))
def pm(m, s): return '%.3f ± %.3f' % (m, s)
print('**Table A: typicality of the sextic rows on slot-selected W (top eigenvalue of the unit-diagonal Gram).**\n')
print('| B | L | P0 (slot primes) | \\|W\\| | log_B\\|W\\| | sextic | MP edge | random W | RMM-S | P(RMM ≥ sextic) | BRM-S P | i.i.d. Schur | P(Schur ≥ sextic) |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|---|')
for d, rho, r in runs:
    st = r['sextic']; rm = r.get('RMM'); br = r.get('BRM'); sc = r.get('SCHUR')
    print('| %d | %d | %d (%d) | %d | %.2f | %.3f | %.3f | %s | %s | %.2f | %s | %s | %s |' % (
        d['B'], d['L'], d['P0'], d['nslot'], r['k'], math.log(r['k']) / math.log(d['B']), st['top'], r['mp'],
        pm(*r['randW_top']), pm(rm['top_mean'], rm['top_std']), rm['frac_ge_sextic'],
        '%.2f' % br['frac_ge_sextic'] if br else '–',
        pm(sc['top_mean'], sc['top_std']) if sc else '–', '%.2f' % sc['frac_ge_sextic'] if sc else '–'))
print('\n**Table B: the centered fourth moment tr(E_W⁴) and its split (design D1, inequality (M₄)).**\n')
print('| B | L | P0 | \\|W\\| | tr(E_W⁴) | 2\\|W\\|³/S² | sextic/RMM (q = 2) | backtracking: sextic / RMM | 4-cycles: sextic / RMM ± sd | 4-cycles / no-cancellation | row msq: mean, max / (\\|W\\|/S) |')
print('|---|---|---|---|---|---|---|---|---|---|---|')
for d, rho, r in runs:
    st = r['sextic']; c = r.get('cycles'); rm = r['RMM']
    if 'cmom' not in st or c is None: continue
    cs, cm = c['sextic'], c['model_mean']; ws = r['k'] / st['diag']
    print('| %d | %d | %d | %d | %.3g | %.3g | %.2f | %.3g / %.3g | %.3g / %.3g ± %.2g | %.4f | %.2f, %.2f |' % (
        d['B'], d['L'], d['P0'], r['k'], st['cmom']['2'], r['cert4']['pred4'], rm['cmom_ratio']['2'],
        cs['bt'], cm['bt'], cs['cy'], cm['cy'], c['model_cy_std'], cs['cy'] / cs['cyabs'],
        cs['rmean'] / ws, cs['rmax'] / ws))
print('\n**Table C: moment certificates against the true top eigenvalue (model moments, RMM-S).**\n')
print('| B | L | P0 | \\|W\\| | (E tr H^p)^{1/p}/top, p = 4 | p = 12 | p = 35 | uncentered tr ratio sextic/RMM, p = 35 | centered 1 + tr(E⁴)^{1/4} / top |')
print('|---|---|---|---|---|---|---|---|---|')
for d, rho, r in runs:
    st = r['sextic']; c = r['cert_over_top']; rm = r['RMM']
    c4 = '%.2f' % (r['cert4']['cert_top'] / st['top']) if 'cert4' in r else '–'
    print('| %d | %d | %d | %d | %.2f | %.2f | %.2f | %.2f | %s |' % (
        d['B'], d['L'], d['P0'], r['k'], c['4'], c['12'], c['35'], rm['mom_ratio']['35'], c4))
