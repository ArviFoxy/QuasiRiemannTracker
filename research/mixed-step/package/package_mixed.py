"""Assemble the mixed-step submission as ONE self-contained Lean package
`Submissions.arvi_mixed_step_20261026` (new submission, not an update of PR 76).

Sources (in the Lake project LAKE):
  * the development tree   Submissions/arvi_mixed_step                    (prefix renamed)
  * the final return       Submissions/arvi_mixed_step_20261026           (already at the target prefix)
  * PR 76's package        Submissions/arvi_repeated_marks_on_sil_face_20261025 (vendored, prefix renamed;
                           its own chain/return are not in the import closure and are not copied)
Collet's tree and the baseline (both merged upstream) are dependencies, imported unchanged.

The import closure of the ROOT modules is computed over the three trees; every module in it is copied
to TARGET/<same relative path>, with `import` lines rewritten to the target prefix. Two different source
modules mapping to the same target path is an error.

usage: python3 package_mixed.py LAKE TARGET_DIR ROOT_MODULE...   (roots given with any of the 3 prefixes)
"""
import os, re, sys, shutil, collections

DEV = 'Submissions.arvi_mixed_step'
RET = 'Submissions.arvi_mixed_step_20261026'
PR76 = 'Submissions.arvi_repeated_marks_on_sil_face_20261025'
TARGET = RET
TREES = [RET, DEV, PR76]          # RET first: 'arvi_mixed_step_20261026' also starts with DEV's text
IMPORT = re.compile(r'^import\s+(\S+)', re.M)


def tree_of(mod):
    for t in TREES:
        if mod == t or mod.startswith(t + '.'):
            return t
    return None


def rel(mod, t):
    return mod[len(t) + 1:]


def src_path(lake, mod):
    return os.path.join(lake, mod.replace('.', '/') + '.lean')


def target_mod(mod):
    t = tree_of(mod)
    return mod if t is None else TARGET + '.' + rel(mod, t)


def closure(lake, roots):
    seen, order = set(), []
    todo = collections.deque(roots)
    while todo:
        m = todo.popleft()
        if m in seen or tree_of(m) is None:
            continue
        seen.add(m)
        p = src_path(lake, m)
        if not os.path.exists(p):
            raise SystemExit(f"missing module {m} ({p})")
        order.append(m)
        for imp in IMPORT.findall(open(p).read()):
            todo.append(imp)
    return order


def main():
    lake, target_dir = sys.argv[1], sys.argv[2]
    roots = sys.argv[3:]
    mods = closure(lake, roots)
    dest = {}
    for m in mods:
        tm = target_mod(m)
        if tm in dest and dest[tm] != m:
            raise SystemExit(f"path clash: {m} and {dest[tm]} -> {tm}")
        dest[tm] = m
    counts = collections.Counter(tree_of(m) for m in mods)
    print("closure:", len(mods), dict(counts))
    for tm, m in sorted(dest.items()):
        text = open(src_path(lake, m)).read()
        text = IMPORT.sub(lambda mo: 'import ' + target_mod(mo.group(1)), text)
        out = os.path.join(target_dir, tm.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(out), exist_ok=True)
        if not (os.path.exists(out) and open(out).read() == text):
            open(out, 'w').write(text)
    # stale files: target-tree files not in the closure
    stale = []
    root = os.path.join(target_dir, TARGET.replace('.', '/'))
    for d, _, fs in os.walk(root):
        for f in fs:
            if f.endswith('.lean'):
                mod = os.path.relpath(os.path.join(d, f), target_dir)[:-5].replace('/', '.')
                if mod not in dest:
                    stale.append(mod)
    print("stale (not in closure):", len(stale))
    for s in stale[:20]:
        print("  ", s)


if __name__ == '__main__':
    main()
