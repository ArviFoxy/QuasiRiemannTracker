import numpy as np, counts as C, supply as S
k = 0.75
print('check: R_supply(sigma) vs rowCount (sigma = 7/37 and 1.0), partial False/True')
for nu in (0.5, 0.55, 0.6, 0.65, 0.7, 0.75):
    for p in (0.0, 0.1, 0.2, 0.35, 0.5):
        rc = C.rowCount(nu, p, k)
        r1 = S.R_supply(nu, p, k, 7/37, False)[0]
        r2 = S.R_supply(nu, p, k, 1.0, False)[0]
        r3 = S.R_supply(nu, p, k, 7/37, True)[0]
        flag = '' if max(abs(r1-rc), abs(r2-rc), abs(r3-rc)) < 1e-9 else '   <-- diff'
        print('nu=%.2f p=%.2f rowCount=%.8f  sigma7/37=%.8f  sigma1=%.8f  partial7/37=%.8f%s' % (nu, p, rc, r1, r2, r3, flag))
print()
print('limited supply at nu=0.6, p=0.5 (B2: sigma 0.12 -> 0.45755; 0.09 -> 0.45958; 0.07 -> 0.46711 with kappa=0.74791)')
k = 0.74791
for sg in (0.2, 0.12, 0.09, 0.07, 0.05, 0.03):
    print('  sigma=%.2f  full-width-only %.5f   partial-z %.5f   rowCount %.5f  rho %.5f' % (sg, S.R_supply(0.6, 0.5, k, sg, False)[0], S.R_supply(0.6, 0.5, k, sg, True)[0], C.rowCount(0.6, 0.5, k), C.rho(0.6)))
