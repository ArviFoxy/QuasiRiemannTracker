# Top-row (d=h) comparison of bad-row Hoelder shapes at the model binding point
# (faces 58/52, s_P=9/200, reproduces 0.8747289): h=0.802, ell=0.167751, delta=0.455, p=1/2, R=0.60369, C=0.03306
h, ell, dl, p, R, C = 0.802, 0.167751, 0.455, 0.5, 0.60369, 0.03306
dp = dl*p; n0 = 2*ell/h
dEdth = 0.222   # model: dtheta/d(uniform E shift) at s_P=9/200
E4  = dp*ell + h/4 + 3*h*R/4 - dp*C/2            # current: #C^{3/4}(sum|N|^4|Q_sel|^2)^{1/4}, slots pointwise
E2  = h/2 + h*R/2                                 # #C^{1/2}(sum|N Q_all|^2)^{1/2}: full slot credit, 2nd moment
Epw = dp*ell + h*R + dl*n0*h/2                    # pointwise numerator |S(U^n0)|^2 <= U^{delta n0}
print(f"n0={n0:.4f}")
print(f"E(4th,current) part = {E4:.5f}")
print(f"E(2nd/inverse-face shape) part = {E2:.5f}  diff vs current = {E2-E4:+.5f}  -> dtheta ~ {dEdth*(E2-E4):+.5f}")
print(f"E(pointwise numerator) part = {Epw:.5f}  diff vs current = {Epw-E4:+.5f}")
print(f"break-even R for 2nd-moment shape: {1-4*dp*(ell-C/2)/h:.4f}")
# frozen sub-slot of width lf: room +lf (value 0.0626/unit), low bound + lf/2 (dtheta/dlow = 0.78)
print("frozen slot dtheta per unit width:", 0.78*0.5 - 0.0626)
print("over-threshold energy: break-even low loss per unit excess:", 0.0626/0.78)
