"""Fork Collet's generic return below the coarse parameter bounds (`Geometry.Bounds`).

Collet's transport layer fixes coarse bounds on the return parameters in the class
`Geometry.Bounds` (Record1252270103Return/TransportGeometry.lean): `ell < 0.1677`, `y < 0.466`,
`h < 0.802`, which force `theta > 0.87474167`. This tool re-elaborates every return module that
depends on TransportGeometry (the transport layer, the generic physical return and the physical
schedule; final-stage and intermediate-stage modules excluded) against the class `Geometry.BoundsR`
with relaxed bounds. It supersedes fork_physical.py: the Lemma D edits of fork_physical_patches.py
are applied as well.

Mechanical rules:
  * module `Record1252270103Return.<path>` -> `Submissions.repeated_marks_20261024.ReturnD.<path>`;
  * namespaces are renamed by MAPS (Collet's `Geometry` namespace is kept: `BoundsR` is declared in
    it, and Collet's `h`, `dPlus` are reused); a renamed namespace opens Collet's ancestors, so that
    unforked names still resolve;
  * fully qualified references to forked declarations, and opens of namespaces holding only
    forked declarations, are re-pointed;
  * the class `Geometry.Bounds` and its fields become `Geometry.BoundsR`;
  * `#print axioms` lines are dropped.

usage: python3 fork_transport.py OUTROOT SP
(environment: QRH_RELAXED='h,y,ell' upper bounds of BoundsR; QRH_DMINUS, e.g. 1/2, relaxes the
schedule field `dMinus_lower : 3/4 < dMinus`; both default to the previous output)
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fork_physical_patches as FP
HERE = os.path.dirname(os.path.abspath(__file__))

SRC = '/home/user/QuasiRiemannTracker/submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103'
CPKG = 'Submissions.hailey_collet_1252270103'
PKG = 'Submissions.repeated_marks_20261024'
ROOT_MOD = 'Record1252270103Return.TransportGeometry'
MAPS = [('OAI.SevenEighths.Record1252270103Return', 'OAI.SevenEighths.RepeatedMarksReturn'),
        ('OAI.SevenEighths.Record1252270103TransportLow', 'OAI.SevenEighths.RepeatedMarksTransportLow'),
        ('Record1252270103Return.Transport', 'RepeatedMarksReturn.Transport'),
        ('QRH.Record1252270103Return', 'QRH.RepeatedMarks.Return')]
# identifiers are also written relative to `OAI` or `OAI.SevenEighths` (opened, or as ancestors)
ROOTS = ['QRH.Record1252270103Return', 'OAI.SevenEighths.Record1252270103Return',
         'SevenEighths.Record1252270103Return', 'Record1252270103Return',
         'OAI.SevenEighths.Record1252270103TransportLow', 'SevenEighths.Record1252270103TransportLow',
         'Record1252270103TransportLow']
IMPLIED = ['', 'QRH.', 'OAI.', 'OAI.SevenEighths.']
KEEP_NS = ('QRH.Record1252270103Return.Geometry',)
EXCLUDE = {'Record1252270103Return.FinalSchedule', 'Record1252270103Return.FinalRows',
           'Record1252270103Return.EndpointFromSources', 'Record1252270103Return.EndpointFromGlobalSources',
           'Record1252270103Return.EndpointFromNumerator', 'Record1252270103Return.TransportInstances'}
# the relaxed bounds (upper ends of h, y, ell): the default is PR 73's, where theta = 8747289/10^7 at
# h = 401/500 has ell = 0.16775, y = 0.46650; QRH_RELAXED='h,y,ell' overrides it
RELAXED = dict(zip(('h', 'y', 'ell'), os.environ.get('QRH_RELAXED', '803/1000,467/1000,1678/10000').split(',')))
# the lower bound of the physical schedule's switch (field `dMinus_lower` of Schedule.lean): Collet's
# `3/4<dMinus` unless QRH_DMINUS is set (e.g. 1/2; every use of the field needs only 1/2<dMinus:
# GenericFeedback, PhysicalDirect/Geometry, Active, SelectedBin, SourceSelection). cert_return.py
# reads the same flag for its receipt `dMinus_lower_3_4`.
DMINUS = os.environ.get('QRH_DMINUS')
TRANSPORT_GEOMETRY_PATCH = (
    '''namespace QRH.Record1252270103Return.Geometry
noncomputable section
variable [Parameters]
def h : ℝ := 1+ell-x
def dPlus : ℝ := h+1/10000000000
class Bounds : Prop where
 theta_bounds : 874/1000<theta ∧ theta<7/8
 h_interval : 793/1000<h ∧ h<802/1000
 ly_coarse : 458/1000<y ∧ y<466/1000
 ell_interval : 1672/10000<ell ∧ ell<1677/10000
''',
    f'''namespace QRH.Record1252270103Return.Geometry
noncomputable section
variable [Parameters]
/-- Collet's coarse parameter bounds (`Bounds`, Record1252270103Return/TransportGeometry.lean),
relaxed at the upper ends of `h`, `y` and `ell`. -/
class BoundsR : Prop where
 theta_bounds : 874/1000<theta ∧ theta<7/8
 h_interval : 793/1000<h ∧ h<{RELAXED['h']}
 ly_coarse : 458/1000<y ∧ y<{RELAXED['y']}
 ell_interval : 1672/10000<ell ∧ ell<{RELAXED['ell']}
''')
BOUND_FIELDS = ('theta_bounds', 'h_interval', 'ly_coarse', 'ell_interval', 'small_saving', 'floor_margin')
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)?(?:noncomputable\s+)?(?:nonrec\s+)?"
                  r"(?:def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque)\s+([A-Za-z_][A-Za-z_0-9.'!?]*)")
HDR = ("/- Repeated marks: fork of Collet's generic return module {m} (Record1252270103Return,\n"
       "Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the\n"
       "relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/\n")


def write_if_changed(path, text):
    """Write only when the content changes, so that unchanged modules keep their build."""
    if os.path.exists(path) and open(path).read() == text:
        return
    open(path, 'w').write(text)


def all_modules():
    mods = {}
    base = os.path.join(SRC, 'Record1252270103Return')
    for d, _, fs in os.walk(base):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(d, f)
                m = os.path.relpath(p, SRC)[:-5].replace('/', '.')
                mods[m] = [l.split()[1][len(CPKG) + 1:] for l in open(p) if l.startswith('import ' + CPKG + '.')]
    return mods


def forked_modules(mods):
    rev = collections.defaultdict(set)
    for m, ds in mods.items():
        for d in ds:
            rev[d].add(m)
    seen, todo = {ROOT_MOD}, [ROOT_MOD]
    while todo:
        x = todo.pop()
        for y in rev[x]:
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return {m for m in seen if m not in EXCLUDE and '.IntermediateCount.' not in m}


def declarations(text):
    """(namespace, full name) of every declaration, tracking `namespace`/`end`."""
    out, stack = [], []
    for line in text.split('\n'):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r'^end\s+(\S+)', line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(1)
            if name.startswith('_root_.'):
                out.append(('', name[7:]))
            else:
                ns = '.'.join(stack)
                out.append((ns, (ns + '.' + name) if ns else name))
    return out


def under(full, prefix):
    return full == prefix or full.startswith(prefix + '.')


def map_full(full):
    if any(under(full, k) for k in KEEP_NS):
        return full
    for old, new in MAPS:
        if under(full, old):
            return new + full[len(old):]
    return full


def new_module(m):
    return f'{PKG}.ReturnD.' + m[len('Record1252270103Return.'):]


def rename_bounds(text):
    text = re.sub(r"(?<![A-Za-z_0-9'])((?:QRH\.Record1252270103Return\.)?Geometry\.)Bounds(?![A-Za-z_0-9'])",
                  r'\1BoundsR', text)
    text = re.sub(r"(?<![A-Za-z_0-9'.])Bounds\.(" + '|'.join(BOUND_FIELDS + ('mk',)) + r")(?![A-Za-z_0-9'])",
                  r'BoundsR.\1', text)
    text = re.sub(r"@Bounds(?![A-Za-z_0-9'])", '@BoundsR', text)
    return text


def build_context():
    """The forked modules, their declarations, and the re-pointing of qualified names."""
    mods = all_modules()
    fork = sorted(forked_modules(mods))
    texts = {m: open(os.path.join(SRC, m.replace('.', '/') + '.lean')).read() for m in fork}
    fork_names, ns_forked, ns_unforked = set(), set(), set()
    for m in mods:
        text = texts.get(m) or open(os.path.join(SRC, m.replace('.', '/') + '.lean')).read()
        for ns, full in declarations(text):
            if m in texts:
                fork_names.add(full)
                ns_forked.add(ns)
            else:
                ns_unforked.add(ns)
    fork_names = {n for n in fork_names if map_full(n) != n}
    only_forked = {ns for ns in ns_forked if ns not in ns_unforked and map_full(ns) != ns}
    # every namespace prefix (registered by Lean) holding only forked declarations
    prefixes = collections.defaultdict(lambda: [False, False])
    for ns in ns_forked | ns_unforked:
        parts = ns.split('.')
        for k in range(1, len(parts) + 1):
            pre = '.'.join(parts[:k])
            prefixes[pre][0 if ns in ns_forked else 1] = True
    only_forked |= {p for p, (f, u) in prefixes.items() if f and not u and map_full(p) != p}
    roots = '|'.join(re.escape(o) for o in sorted(ROOTS, key=len, reverse=True))
    qual = re.compile(r"(?<![A-Za-z_0-9.'])(" + roots + r")(?![A-Za-z_0-9'!?])((?:\.[A-Za-z_][A-Za-z_0-9'!?]*)*)")

    def requal(mt):
        tok = mt.group(1) + mt.group(2)
        parts = tok.split('.')
        for k in range(len(parts), 0, -1):
            rel = '.'.join(parts[:k])
            for imp in IMPLIED:
                cand = imp + rel
                # a name read relative to an ancestor must be a forked declaration itself
                if cand in fork_names or (not imp and cand in only_forked):
                    new = map_full(cand) + tok[len(rel):]
                    return new[len(imp):] if imp and new.startswith(imp) else new
        return tok

    return dict(fork=fork, texts=texts, fork_names=fork_names, only_forked=only_forked,
                requalify=lambda text: qual.sub(requal, text))


def relax_literals(rel, body):
    """Restatements of the coarse bounds as literals."""
    if rel in ('TransportGeometry', 'Transport.FinalFixedHigh'):
        body = body.replace('1677/10000', RELAXED['ell']).replace('h<802/1000', 'h<' + RELAXED['h'])
        body = body.replace('ly<466/1000', 'ly<' + RELAXED['y'])
    return body


def main():
    out, sp = sys.argv[1], sys.argv[2]
    patches = FP.patches(sp)
    if DMINUS is not None:
        patches['Schedule'] = patches.get('Schedule', []) + [(
            ' dMinus_lower:3/4<dMinus\n',
            f' /-- Relaxed from Collet\'s `3/4<dMinus`: every use needs only `1/2<dMinus`. -/\n'
            f' dMinus_lower:{DMINUS}<dMinus\n')]
    ctx = build_context()
    fork, texts, only_forked = ctx['fork'], ctx['texts'], ctx['only_forked']
    for m in fork:
        rel = m[len('Record1252270103Return.'):]
        path = os.path.join(out, 'ReturnD', rel.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(path), exist_ok=True)
        if rel in FP.HAND:
            write_if_changed(path, rename_bounds(open(os.path.join(HERE, FP.HAND[rel])).read()))
            continue
        t = texts[m]
        lines = []
        stack, new_stack = [], []   # Collet's namespaces, and the emitted ones
        for line in t.split('\n'):
            mi = re.match(r'^import\s+(\S+)', line)
            if mi:
                tgt = mi.group(1)
                if tgt.startswith(CPKG + '.') and tgt[len(CPKG) + 1:] in texts:
                    line = 'import ' + new_module(tgt[len(CPKG) + 1:])
                lines.append(line)
                continue
            if line.startswith('#print axioms'):
                continue
            mn = re.match(r'^namespace\s+(\S+)\s*$', line)
            if mn:
                old_full = '.'.join(stack + [mn.group(1)])
                new_full = map_full(old_full)
                cur_new = map_full('.'.join(stack)) if stack else ''
                relname = new_full[len(cur_new) + 1:] if cur_new and new_full.startswith(cur_new + '.') else new_full
                stack.append(mn.group(1))
                new_stack.append(relname)
                lines.append(f'namespace {relname}')
                if new_full != old_full:
                    parts = old_full.split('.')
                    opens = ['.'.join(parts[:k]) for k in range(1, len(parts))]
                    opens = [o for o in opens if o.startswith('QRH.') and o not in only_forked and '.' in o]
                    if opens:
                        lines.append('open ' + ' '.join(opens))
                continue
            me = re.match(r'^end\s+(\S+)\s*$', line)
            if me and stack and stack[-1] == me.group(1):
                stack.pop()
                lines.append(f'end {new_stack.pop()}')
                continue
            mo = re.match(r'^(\s*open\s+)(.*)$', line)
            if mo and not line.lstrip().startswith('open scoped'):
                toks = []
                cur = '.'.join(stack)
                scopes = [cur[:i] for i in range(len(cur), 0, -1) if i == len(cur) or cur[i] == '.']
                for tok in mo.group(2).split():
                    cands = [sc + '.' + tok for sc in scopes] + [imp + tok for imp in IMPLIED]
                    hit = next((c for c in cands if c in only_forked), None)
                    toks.append(map_full(hit) if hit else tok)
                lines.append(mo.group(1) + ' '.join(toks))
                continue
            lines.append(ctx['requalify'](line))
        body = '\n'.join(lines)
        if rel == 'TransportGeometry':
            old_g, new_g = TRANSPORT_GEOMETRY_PATCH
            if body.count(old_g) != 1:
                raise SystemExit('TransportGeometry patch does not apply')
            body = body.replace(old_g, new_g)
            body = body.replace(f'import {CPKG}.Record1252270103Return.IntermediateGeometry',
                                f'import {CPKG}.Record1252270103Return.IntermediateGeometry\n'
                                f'import {CPKG}.Record1252270103Return.TransportGeometry', 1)
        body = relax_literals(rel, rename_bounds(body))
        for old, new in FP.GLOBAL:
            body = body.replace(old, new)
        for old, new in patches.get(rel, []):
            if body.count(old) != 1:
                raise SystemExit(f'patch for {rel} applies {body.count(old)} times:\n{old}')
            body = body.replace(old, new)
        write_if_changed(path, HDR.format(m=rel) + body)
    print(f"forked {len(fork)} modules, {len(ctx['fork_names'])} declarations, {len(only_forked)} namespaces re-pointed")


if __name__ == '__main__':
    main()
