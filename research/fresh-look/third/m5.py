import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from m2 import theta
bar = 0.8733819666133 - 5e-5
for Lc, Lp in ((1.9185, 2.0001), (1.9185, 1.9597), (1.9185, 1.9461), (1.9323, 1.9597), (1.9406, 1.9461), (1.9461, 1.9461)):
    t = theta(0.99999, Lc, 0.99999, Lp, capc=0.16)
    print('count Lambda %.4f, physical Lambda %.4f: theta* %.8f  vs bar %+.2e' % (Lc, Lp, t, t - bar))
