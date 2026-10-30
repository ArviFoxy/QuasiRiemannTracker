import slotcost as S
cap = lambda L: 0.1 + 0.06 * (5143 / 2000 - L)
B, h = 0.99999, 0.8097
base = S.theta_star(h, B, 2.0001, cap(2.0001), 2.0)
print('base', base)
for c in (1.96, 1.94, 1.92, 1.90, 1.85, 1.8):
    both = S.theta_star(h, B, 2.0001 * c / 2, cap(2.0001), c)
    inv = S.theta_star(h, B, 2.0001, cap(2.0001), c)
    face = S.theta_star(h, B, 2.0001 * c / 2, cap(2.0001), 2.0)
    print('c %.3f: all %+.2e  inverse-only %+.2e  faces-only %+.2e' % (c, both-base, inv-base, face-base))
