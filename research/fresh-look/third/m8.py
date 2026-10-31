import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from m7 import binding_info
for Lc in (1.8623,):
    th, rows = binding_info(0.99999, Lc, 0.99999, 2.0001, capc=0.165)
    print('count Lambda %.4f: theta %.8f (bar 0.87333197)' % (Lc, th))
    zs = [r[3] for r in rows]; print('   read-point z range near binding: %.4f .. %.4f' % (min(zs), max(zs)))
    for r in rows: print('   p %.3f delta %.4f  m* %.4f  z %.4f' % r)
