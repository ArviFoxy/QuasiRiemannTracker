from fractions import Fraction as F
c = F(25201,200000); h = F(8053,10000)
theta = 1-c; ell = 4*c-F(1,3); x = 1+ell-h; y = h-2*ell; kappa = 1-2*c
dPlus = h+F(1,10**10)
signalShift = -(F(5,6)-x/3-ell/6)
signal = theta+signalShift
print("theta=%s=%.7f ell=%.7f x=%.7f y=%.7f h=%.5f dPlus=%.10f" % (theta, float(theta), float(ell), float(x), float(y), float(h), float(dPlus)))
print("BoundsN margins:")
print("  theta > 873/1000 : margin %.6f" % float(theta-F(873,1000)))
print("  theta < 7/8      : margin %.6f" % float(F(7,8)-theta))
print("  793/1000 < h     : margin %.6f ; h < 806/1000: margin %.6f" % (float(h-F(793,1000)), float(F(806,1000)-h)))
print("  458/1000 < y     : margin %.6f ; y < 467/1000: margin %.6f" % (float(y-F(458,1000)), float(F(467,1000)-y)))
print("  1672/10000 < ell : margin %.6f ; ell < 171/1000: margin %.6f" % (float(ell-F(1672,10000)), float(F(171,1000)-ell)))
ss = y/2 - h*(F(17,50)-F(1,6)) - F(1,50)
print("  small_saving 7/100 < y/2-h(17/50-1/6)-1/50 = %.6f : margin %.6f" % (float(ss), float(ss-F(7,100))))
fm_lhs = F(4,25)*x - F(3,20) - F(51,100)*y + F(67,100)*dPlus - F(3,20)*ell
fm_rhs = signal - F(1,200)
print("  floor_margin lhs=%.6f <= rhs=%.6f : margin %.6f" % (float(fm_lhs), float(fm_rhs), float(fm_rhs-fm_lhs)))
# theta at which ell<171/1000 fails
print("ell<0.171  <=> theta > %.6f" % ((11/3-0.171)/4))
print("PR76 BoundsR : theta>0.874, h<0.803, ell<0.169 ; at PR83 values h=%.4f ell=%.4f theta=%.6f -> fails (theta<0.874, h>0.803, ell>0.169)" % (float(h), float(ell), float(theta)))
