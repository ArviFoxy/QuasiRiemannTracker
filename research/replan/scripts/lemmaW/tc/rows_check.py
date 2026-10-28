# Exact check: the Bernstein minima m of PR 86's 31 certified rows (Return/Rows/Edge_*.lean) versus our polynomials
import re, glob, os
from fractions import Fraction as Fr
import pr86, cert_return as CR
U86 = '$SCRATCH/upstream/submissions/2026-10-28-density-split-fine-chain/src/Submissions/density_split_fine_chain/Return/Rows'
cfg = pr86.Cfg()
pr86.apply_globals(cfg)
G = pr86.geometry(cfg)
edges = {nm: (d, C) for nm, d, C in pr86.edge_list(cfg, G)}
cands = {nm: br for nm, br, meta in pr86.candidate_list(cfg, G)}
brmap = {'old': 'old', 'C': 'C', 'capP': 'Pcap'}
pat = re.compile(r'theorem (row\d+\w*)_identity \(δ p : ℝ\) : rowMargin \.(\w+) \.(\w+) δ p =\s*\n\s*Record12518109\.Bernstein\.bsum (\d+) (\d+) \(([^:]+):ℝ\) \w+ \(([^:]+):ℝ\) \(([^:]+):ℝ\) \(([^:]+):ℝ\) \(([^:]+):ℝ\)')
tot = ok = 0
worst = None
for f in sorted(glob.glob(U86 + '/Edge_*.lean')):
    txt = open(f).read()
    for m in pat.finditer(txt):
        name, edge, br, n1, n2, mv, d0, d1, p0, p1 = m.groups()
        mv, d0, d1, p0, p1 = (Fr(x) for x in (mv, d0, d1, p0, p1))
        d, C = edges[edge]
        rp = CR.return_poly(cands[brmap[br]], G, d, C)
        mine = CR.bernstein_min(rp, ((d0, d1), (p0, p1)))
        tot += 1
        same = (mine == mv)
        ok += same
        rel = float((mine - mv)/mv) if mv else 0.0
        if not same and (worst is None or abs(rel) > abs(worst[1])): worst = (name, rel, mine, mv)
        if edge == 'newTop' and name in ('row021', 'row023a', 'row023b', 'row024', 'row025'):
            print('  %-8s %-9s %-5s delta[%.4f,%.4f] p[%.4f,%.4f]  m_lean=%.3e  m_mine=%.3e  %s' % (name, edge, br, float(d0), float(d1), float(p0), float(p1), float(mv), float(mine), 'EXACT' if same else 'differs %.2e rel' % rel))
print('rows compared: %d, exactly equal Bernstein minima: %d' % (tot, ok))
if worst: print('largest relative difference:', worst[0], worst[1])
