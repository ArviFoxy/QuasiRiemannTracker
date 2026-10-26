"""Put the original file's copyright line verbatim first in every ForkMx module (Apache-2.0 §4).

A ForkMx module `ForkMx/<rel>.lean` forks Collet's `<rel>.lean` (and possibly PR 76's
`Fork/<rel>.lean`). Its header must start with the first line of Collet's file verbatim, followed
by the fork note. The script rewrites a header of the form
  /- Mixed step (L4/L5, ...): fork of ... -/
into
  /- <Collet's first line>
  Mixed step (L4/L5, ...): fork of ... -/
and leaves files that already start with the copyright line alone.
usage: python3 fix_headers.py FORKMX_ROOT
Then run add_mod_line.py on the development root (our own `Modifications Copyright` notice, Apache-2.0 §4).
"""
import os, sys
CROOT = '/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103'
root = sys.argv[1]
for d, _, fs in os.walk(root):
    for f in fs:
        if not f.endswith('.lean'):
            continue
        p = os.path.join(d, f)
        rel = os.path.relpath(p, root)
        src = os.path.join(CROOT, rel)
        if not os.path.exists(src):
            print('NO SOURCE', rel); continue
        first = open(src).readline().rstrip('\n')
        if not first.startswith('/- Copyright'):
            print('SOURCE HAS NO COPYRIGHT FIRST LINE', rel, first); continue
        t = open(p).read()
        if t.startswith(first):
            continue
        assert t.startswith('/- '), rel
        # the copyright line may carry text after "Apache-2.0." on the same line; keep it verbatim
        t = first + '\n' + t[3:]
        open(p, 'w').write(t)
        print('fixed', rel)
