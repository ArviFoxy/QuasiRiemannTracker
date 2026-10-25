"""Symbolic check: generalized slot operation  I(X p^a1, Y p^a2, Z p^a3) on marked terms
(rescaled partner adjusted to cancel the scalar part) is a pure reparametrization.
Exponents in log_Z units; slot length ell; bad rows at the top of the dual range (d = h).
"""
import sympy as sp
x,y,ell,a1,a2,a3,th,a,dp,R,h = sp.symbols('x y ell a1 a2 a3 theta a dp R h', real=True)
# --- low side: signal X^{1/3} Z^{th-5/6} P^{1 + a1/3 + a3(th-5/6) - th};  low bound X'^{1/2}(Y'/X')^{1/12}
sig  = x/3 + th - sp.Rational(5,6) + ell*(1 + a1/3 + a3*(th - sp.Rational(5,6)) - th)
low  = x/2 + (y - x)/12 + ell*(sp.Rational(5,12)*a1 + a2/12)
# energy tight:  x + y = 1 + (a3 - a1 - a2 - 2) ell
ysub = 1 + (a3 - a1 - a2 - 2)*ell - x
thlow = sp.solve(sp.Eq(sig.subs(y, ysub), low.subs(y, ysub)), th)[0]
print("theta_low =", sp.simplify(thlow))
print("  equals reparam 11/12 - ell'/4 with ell'=ell/(1+(a3-1)ell):",
      sp.simplify(thlow - (sp.Rational(11,12) - ell/(1+(a3-1)*ell)/4)) == 0)
# --- high side, top rows: log(bad/signal) at beta = theta
# slot exponent per prime at bad rows (Re s=a, Re w=1/2, z cancels at top), sqrt cancellation + amplitude dp
hh = 1 - x + (a3 - a1)*ell               # dual range
slot_bad = sp.Rational(1,2) + dp + a1/2 - a2/2 - a3 + (a3 - 1)*a
bad = a - 1 + x/2 - y/2 + ell*slot_bad + hh*(1 + 3*R)/4   # X^{1/2} Z^{a-1} Y^{-1/2} * slots * Hoelder
signal = x/2 + th - 1 + (1 - x)/6 + ell*(1 + a1/3 - sp.Rational(5,6)*a3 + (a3-1)*th)
diff = sp.expand((bad - signal).subs(y, ysub).subs(x, sp.solve(sp.Eq(hh, h), x)[0]))
print("log(bad/signal) =", sp.collect(sp.simplify(diff), [ell, h]))
print("  a1,a2 present?", diff.has(a1), diff.has(a2))
