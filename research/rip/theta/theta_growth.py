"""Growth table of the low-frequency outlier from the theta_top_free*.log files.

For each size B = L it reads the top eigenvalues of E^H E / S printed by theta_top_free.py / theta_top_free2.py (sextic,
masked random phases on E's zero pattern, RCHAR), and prints
  * the excess of the sextic top over the masked random edge (mean of the random seeds, with their sd),
  * the implied rank-one spike strength theta from lambda / lambda_edge = (sqrt(theta) + 1/sqrt(theta))^2 / 4, i.e.
    sqrt(theta) = sqrt(r) + sqrt(r - 1) with r = lambda / lambda_edge,
  * the local slopes d log theta / d log B between consecutive sizes (Theta_6 caps the excess rate at 1/6),
  * the same excess for RCHAR (reciprocity broken), which should sit at 0.
When a size has several logs the one with the most masked-random samples is used.

The adjacent-size slopes are noisy (the sextic top is one deterministic matrix per size and moves by a few percent with
the arithmetic of B), so the script also prints the slopes on the grid 3e3, 1e4, 3e4, 1e5, 3e5 (the journal's grid) and
least-squares slopes of log theta against log B over the sizes >= B_min, with their standard errors.

usage: python3 -I theta_growth.py [log ...]      (default: every theta_top_free*_B*.log in this directory)
"""
import os, sys, re, glob, math
sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
logs = sys.argv[1:] or sorted(glob.glob(os.path.join(HERE, 'theta_top_free*_B*.log')))
num = re.compile(r'\[([^\]]*)\]')


def parse(path):
    d = dict(sextic=None, random=[], rchar=[], R=None, S=None)
    for line in open(path):
        m = re.match(r'B=(\d+) L=(\d+)\s+R=(\d+) rows\s+S=(\d+) sources', line)
        if m:
            d['B'] = int(m.group(1)); d['R'] = int(m.group(3)); d['S'] = int(m.group(4))
        m = num.search(line)
        if not m:
            continue
        try:
            vals = [float(t) for t in m.group(1).split()]
        except ValueError:
            continue
        if line.startswith('sextic E'):
            d['sextic'] = vals
        elif line.startswith('masked random'):
            d['random'].append(vals)
        elif line.startswith('RCHAR'):
            d['rchar'].append(vals)
    return d


def spike(r):
    return (math.sqrt(r) + math.sqrt(r - 1.0)) ** 2 if r > 1 else float('nan')


best = {}
for path in logs:
    d = parse(path)
    if 'B' not in d or d['sextic'] is None or not d['random']:
        continue
    if d['B'] not in best or len(d['random']) > len(best[d['B']][1]['random']):
        best[d['B']] = (path, d)

print('%8s %6s %6s | %6s %6s %6s %6s | %14s | %7s | %7s %12s %6s | %8s | %s' %
      ('B=L', 'R', 'S', 'lam1', 'lam2', 'lam3', 'lam4', 'masked random', 'RCHAR', 'excess', 'theta', 'slope', 'RCHAR exc', 'log'))
prev = None
thetas = {}
for B in sorted(best):
    path, d = best[B]
    ev = d['sextic']
    rnd = np.array([e[0] for e in d['random']])
    edge = rnd.mean(); sd = rnd.std(ddof=1) if len(rnd) > 1 else float('nan')
    r = ev[0] / edge
    th = spike(r)
    slope = (math.log(th / prev[1]) / math.log(B / prev[0])) if prev else float('nan')
    rc = np.array([e[0] for e in d['rchar']]) if d['rchar'] else np.array([])
    se = sd / math.sqrt(len(rnd)) if len(rnd) > 1 else float('nan')
    dth = th * (r / math.sqrt(r * (r - 1.0))) * (se / edge) if r > 1 else float('nan')       # from the edge's standard error
    print('%8d %6s %6s | %6.3f %6.3f %6.3f %6.3f | %7.4f +-%.4f (%d) | %7s | %+6.1f%% %6.3f+-%.3f %6.3f | %8s | %s' %
          (B, d['R'], d['S'], ev[0], ev[1], ev[2], ev[3], edge, sd, len(rnd),
           ('%.4f' % rc.mean()) if len(rc) else '-', 100 * (r - 1), th, dth, slope,
           ('%+.2f%%' % (100 * (rc.mean() / edge - 1))) if len(rc) else '-', os.path.basename(path)))
    prev = (B, th)
    thetas[B] = th

print('\nslopes d log theta / d log B on the grid 3e3, 1e4, 3e4, 1e5, 3e5 (those present):')
grid = [b for b in (3000, 10000, 30000, 100000, 300000) if b in thetas]
for a, b in zip(grid[:-1], grid[1:]):
    print('   %7d -> %7d: %.3f' % (a, b, math.log(thetas[b] / thetas[a]) / math.log(b / a)))
if 200000 in thetas and 100000 in thetas:
    print('   %7d -> %7d: %.3f' % (100000, 200000, math.log(thetas[200000] / thetas[100000]) / math.log(2.0)))
print('fits over the sizes >= B_min (theta = a B^g + b; rms of the residuals in theta):')
for bmin in (3000, 10000):
    Bs = np.array([b for b in sorted(thetas) if b >= bmin], float); th = np.array([thetas[int(b)] for b in Bs])
    if len(Bs) < 4:
        continue
    out = []
    for g in (1.0 / 6.0, None):
        best = None
        for gg in ([g] if g else np.linspace(0.05, 0.6, 111)):
            Amat = np.vstack([Bs ** gg, np.ones_like(Bs)]).T
            coef = np.linalg.lstsq(Amat, th, rcond=None)[0]
            rms = math.sqrt(np.mean((th - Amat @ coef) ** 2))
            if best is None or rms < best[0]:
                best = (rms, gg, coef[0], coef[1])
        out.append(best)
    pw = np.polyfit(np.log(Bs), np.log(th), 1)
    pr = math.sqrt(np.mean((th - np.exp(np.polyval(pw, np.log(Bs)))) ** 2))
    print('   B >= %6d: pure power  theta = %.3f B^%.3f (rms %.3f);  g = 1/6 with offset: theta = %.3f B^(1/6) %+.3f (rms %.3f);  '
          'free g with offset: g = %.3f, a = %.3f, b = %+.3f (rms %.3f)' %
          (bmin, math.exp(pw[1]), pw[0], pr, out[0][2], out[0][3], out[0][0], out[1][1], out[1][2], out[1][3], out[1][0]))
print('least-squares slope of log theta on log B (standard error), sizes >= B_min:')
for bmin in (3000, 10000, 30000, 100000):
    xs = np.array([math.log(b) for b in sorted(thetas) if b >= bmin]); ys = np.array([math.log(thetas[b]) for b in sorted(thetas) if b >= bmin])
    if len(xs) >= 3:
        A = np.vstack([xs, np.ones_like(xs)]).T
        coef, res, *_ = np.linalg.lstsq(A, ys, rcond=None)
        resid = ys - A @ coef
        se = math.sqrt(resid @ resid / (len(xs) - 2) / ((xs - xs.mean()) @ (xs - xs.mean())))
        print('   B >= %6d (%d sizes): %.3f +- %.3f' % (bmin, len(xs), coef[0], se))
