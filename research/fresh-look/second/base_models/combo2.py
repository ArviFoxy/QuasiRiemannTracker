from combo import theta_star
base = 0.87338228
for (ci,cf,s) in [(2,1.9,0.80),(2,1.8,0.80),(1.95,2,0.80),(2,1.9,0.77),(1.9,1.9,0.80)]:
    t = theta_star(ci,cf,s); print('ci %.2f cf %.2f s %.3f: %.8f  d_bank %+.2e  d_#97 %+.2e' % (ci,cf,s,t,t-base,t-0.87341198), flush=True)
