import run2
# implementation haircut: PR 86-like gate reserve 1e-5 (instead of 1e-6), floors 0.55 and 0.50, all-on and base
for (f, b, d) in ((0.55, 0, 0.999), (0.50, 0, 0.999)):
    r = run2.run_scenario(1.0, f, b, d, 0.005, tag='_eps1e-5', eps=1e-5)
    print('%-52s theta=%.9f gap=%+.2e  C(L=%.4f,s0=%.4f,%d/%d) P(L=%.3f) [chain %.0fs, return %.0fs]' % (
        r['name'], r['theta'], r['theta'] - run2.BAR, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'], r['t_chain'], r['t_ret']), flush=True)
