import numpy as np, slotcost as S
cap = lambda L: 0.1 + 0.06 * (5143 / 2000 - L)
for h in (0.79, 0.80, 0.8097, 0.82, 0.84, 0.86, 0.90):
    print(h, '%.8f' % S.theta_star(h, 0.99999, 2.0001, cap(2.0001), 2.0))
