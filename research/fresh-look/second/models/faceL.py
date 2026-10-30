# Face slot cost Lambda in both faces (count + physical), incl. the D-R numerology value 5/3. [numerical]
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'base_models'))
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    import worth as W
base = W.theta_star(5/6)[0]
for L in (1.95, 1.9, 1.85, 1.8, 1.75, 5/3):
    t = W.theta_star(5/6, L=L)
    print('Lambda %.4f: theta %.8f dtheta %+.2e' % (L, t[0], t[0]-base))
for L, s in ((1.9, 0.80), (5/3, 5/6), (5/3, 0.80)):
    t = W.theta_star(s, L=L); print('Lambda %.4f long %.3f: dtheta %+.2e' % (L, s, t[0]-base))
