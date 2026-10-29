import run2
r = run2.run_scenario(1.0, 0.60, 1, 1.0, 0.0025)
print('%-52s theta=%.9f gap=%+.2e  C(L=%.4f,s0=%.4f,%d/%d) P(L=%.3f) [chain %.0fs, return %.0fs]' % (
    r['name'], r['theta'], r['theta'] - run2.BAR, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'], r['t_chain'], r['t_ret']), flush=True)
