import re
for line in open('logs/price.log'):
    if 'theta=' not in line: continue
    m = re.match(r'(\S+) (\S+) (\S+) lam=(\S+) (P=\S+): theta=(\S+) \(vs record (\S+)\) \| C step (\d+) L=(\S+) B=(\S+) X_C=(\S+) \| P step (\d+) L=(\S+) B=(\S+) X_P=(\S+)', line)
    if m:
        fn, mode, par, lam, p, th, d, cs, cl, cb, xc, ps, pl, pb, xp = m.groups()
        print('%-22s lam=%s %-16s theta=%s d=%s  C: L=%s B=%s X=%s  P: L=%s B=%s X=%s' % (fn, lam, p, th, d, cl, cb, xc, pl, pb, xp))
