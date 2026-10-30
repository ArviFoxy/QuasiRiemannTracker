"""ppshow.py FILE [kind] -- quick look at one grid file: all columns are F/Dcop (the 'F0/D0cop' column is X alone, no pool)."""
import sys, json, numpy as np
d = json.load(open(sys.argv[1])); kind = sys.argv[2] if len(sys.argv) > 2 else 'smooth'
vn = d['varnames']; ri = [i for i, v in enumerate(vn) if v.startswith('rand')]
print('B=%d R=%d log_B R=%.3f  Sp=%d' % (d['B'], d['R'], d['logB_R'], d['Sp']))
print('%-6s %-5s %-5s %-4s %-5s | %-9s %-7s | %-7s %-12s %-7s %-7s %-7s %-7s | %-7s %-7s' % ('kind','m','s','npl','T','F0/D0cop','SE%','ones','rand(mean+-sd)','t5','t20','gsimp','gcan','ctrl','SEc%'))
for e in d['entries']:
    if e['kind'] != kind: continue
    if e['s'] is None:
        print('%-6s %-5.2f base: nX=%d nk=%d  F0/D0=%.3f F0/D0cop=%.3f' % (kind, e['m'], e['nX'], e['nk'], e['F0']/e['D0'], e['F0']/e['D0cop'])); continue
    F = np.array(e['F']); D = np.array(e['D']); Dc = np.array(e['Dcop']); r = F/Dc
    rr = r[ri]
    print('%-6s %-5.2f %-5.2f %-4d %-5.2f | %-7.3f %-7.1f | %-7.3f %.3f+-%.3f   %-7.3f %-7.3f %-7.3f %-7.3f | %-7.3f %-7.1f' % (
        kind, e['m'], e['s'], e['npool'], e['T'], e['F0']/e['D0cop'], 100*np.array(e['SE'])[0]/F[0], r[0], rr.mean(), rr.std(), r[vn.index('t5')], r[vn.index('t20')], r[vn.index('gauss_simple')], r[vn.index('gauss_canon')], e['Fc']/e['Dccop'], 100*e['SEc']/e['Fc']))
