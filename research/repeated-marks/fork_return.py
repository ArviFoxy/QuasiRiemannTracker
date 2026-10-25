"""Fork Collet's final-stage return modules into QRH.RepeatedMarks.Return.

Generic modules (Geometry classes, CountScheme, PhysicalDirect, Transport, the intermediate stage)
are imported unchanged; the modules below hard-code the final constants and are re-instantiated
with ours.  Usage: python3 fork_return.py GENDIR OUTDIR CAPC CAPP
(GENDIR = output of gen_return_lean.py, i.e. containing FinalReturn/{windows,edges}.lean.part).
An optional fifth argument SC is the constant-width cap of the count windows (default 11/250).
An optional sixth argument SP selects Lemma D: the final stage then uses the generic physical
return forked by fork_physical.py (numerator cap SP, the physical face applied at every shift)
instead of Collet's windowed physical schedule."""
import os, re, sys

SRC = '/home/user/QuasiRiemannTracker/submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103'
CPKG = 'Submissions.hailey_collet_1252270103'
PKG = os.environ.get('QRH_PKG', 'Submissions.repeated_marks_20261024')
NS_OLD, NS_NEW = 'QRH.Record1252270103Return', 'QRH.RepeatedMarks.Return'
FORKED = ['Geometry', 'TransportInstances', 'Conductor', 'CountAdmission', 'CountMonotonicity', 'CountWindows',
          'CountDecode', 'CountWidth', 'FinalWindows', 'SourceInlet', 'WindowSources', 'FinalScheme',
          'FinalEnvelopeBounds', 'FinalEdgeCertificates', 'FinalRows', 'FinalSchedule', 'EndpointFromNumerator',
          'EndpointFromSources', 'EndpointFromGlobalSources']
FINITE = ['ReturnConstants', 'ReturnFormulas', 'ReturnFacts']
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|"
                  r"instance|structure|inductive|class)\s+([A-Za-z_][A-Za-z_0-9.']*)", re.M)
HDR = ('/- Repeated marks: fork of Collet\'s final-stage module {m} (Record1252270103Return, Apache-2.0),\n'
       're-instantiated with the final constants of the repeated-mark graph. -/\n')


def write_if_changed(path, text):
    """Write only when the content changes, so that unchanged modules keep their build."""
    if os.path.exists(path) and open(path).read() == text:
        return
    open(path, 'w').write(text)


def declared(text):
    """full names (relative to the root) declared in a module, tracking namespaces."""
    names, stack = set(), []
    for line in text.split('\n'):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)', line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop(); continue
        m = DECL.match(line)
        if m:
            names.add('.'.join(stack + [m.group(1)]))
    return names


def finite_names():
    out = set()
    for f in FINITE:
        for n in declared(open(f'{SRC}/Record1252270103Finite/{f}.lean').read()):
            out.add(n.split('Record1252270103Finite.', 1)[-1])
    return out


def rewrite(text, fork_names, fin_names):
    lines = []
    for line in text.split('\n'):
        m = re.match(r'^import\s+(\S+)', line)
        if m:
            tgt = m.group(1)
            short = tgt.replace(CPKG + '.', '')
            if short.startswith('Record1252270103Finite.Admission') or re.match(r'Record1252270103Finite\.Return\d+$', short):
                continue
            if short.startswith('Record1252270103Return.') and short.split('.', 1)[1] in FORKED:
                lines.append(f'import {PKG}.FinalReturn.{short.split(".", 1)[1]}'); continue
            if short.startswith('Record1252270103Finite.') and short.split('.', 1)[1] in FINITE:
                lines.append(f'import {PKG}.FinalReturn.{short.split(".", 1)[1]}'); continue
            lines.append(line); continue
        lines.append(line)
    text = '\n'.join(lines)
    # fully qualified references to re-instantiated declarations
    for n in sorted(fork_names, key=len, reverse=True):
        rel = n[len(NS_OLD) + 1:]
        text = re.sub(r'(?<![A-Za-z_0-9.])' + re.escape(n) + r'(?![A-Za-z_0-9\'])', NS_NEW + '.' + rel, text)
    for n in sorted(fin_names, key=len, reverse=True):
        text = re.sub(r'(?<![A-Za-z_0-9.])Record1252270103Finite\.' + re.escape(n) + r'(?![A-Za-z_0-9\'])',
                      NS_NEW + '.' + n, text)
    # namespaces: ours, with Collet's generic declarations opened
    def opener(m):
        extra = f' {NS_OLD}.Geometry' if m.group(1) == '.Geometry' else ''
        return f'namespace {NS_NEW}{m.group(1)}\nopen {NS_OLD}{extra}'
    text = re.sub(r'^namespace ' + re.escape(NS_OLD) + r'(\S*)$', opener, text, flags=re.M)
    text = re.sub(r'^end ' + re.escape(NS_OLD) + r'(\S*)$', lambda m: f'end {NS_NEW}{m.group(1)}', text, flags=re.M)
    text = re.sub(r'^#print axioms ' + re.escape(NS_OLD), '#print axioms ' + NS_NEW, text, flags=re.M)
    # Collet's finite namespace holds only re-instantiated constants here
    def drop_finite(m):
        rest = [t for t in m.group(1).split() if t != 'Record1252270103Finite']
        return ('open ' + ' '.join(rest)) if rest else ''
    text = re.sub(r'^open ([^\n]*)$', drop_finite, text, flags=re.M)
    return text


def strip_block(text, name):
    """remove `namespace name ... end name` (one level) and its axiom prints."""
    text = re.sub(r'^namespace ' + name + r'\n.*?^end ' + name + r'\n', '', text, flags=re.M | re.S)
    return re.sub(r'^#print axioms \S*\.' + name + r'\.\S*\n', '', text, flags=re.M)


def lemma_d(m, text, phys, sP, capP, ft=None):
    """Point the final stage at the forked generic physical return (Lemma D); with `ft`, at the
    generic return forked below the relaxed parameter bounds (fork_transport.py)."""
    for mod in sorted(phys, key=len, reverse=True):
        text = text.replace(f'import {CPKG}.Record1252270103Return.{mod}\n', f'import {PKG}.ReturnD.{mod}\n')
    if ft is not None:
        import fork_transport as FT
        text = FT.rename_bounds(ft['requalify'](text))
    for ns in ('GenericArithmetic.', 'GenericPhysical.PhysicalDirect.', 'GenericPhysical.Scalar.'):
        text = text.replace(f'{NS_OLD}.{ns}', f'{NS_NEW}.{ns}')
    def sub1(old, new):
        nonlocal text
        if text.count(old) != 1:
            raise SystemExit(f'lemma D patch for {m} applies {text.count(old)} times:\n{old}')
        text = text.replace(old, new)
    if m == 'Conductor':
        sub1('noncomputable abbrev cap : ℝ := 1/25', 'noncomputable abbrev cap : ℝ := numeratorCap')
        text = text.replace('(d/25)', '(numeratorCap*d)')
    if m == 'FinalSchedule':
        for field in ('physical_plain_lower', 'physical_plain_upper', 'physical_width_lower', 'shift_bound',
                      'large_shift_reserve'):
            text = re.sub(r'^ ' + field + r' := by\n(?:  [^\n]*\n)+', '', text, count=1, flags=re.M)
        sub1(' small_plain_shortening := by', ' small_plain_global := by')
        text = text.replace('dsimp +instances only [', 'dsimp +instances only [QRH.RepeatedMarks.Return.numeratorCap,')
    if m == 'EndpointFromSources':
        sub1(""" have hr : physicalWindow.Restricts GenericPhysical.PhysicalDirect.physicalFace := by
  change physicalWindow.Restricts
   ⟨QRH.RepeatedMarks.Return.physicalB,QRH.RepeatedMarks.Return.physicalLambda,2/5,11/25,17/500,1/25⟩
  constructor <;> norm_num [physicalWindow]""",
             f""" have hr : physicalGlobal.Restricts GenericPhysical.PhysicalDirect.physicalFace := by
  change physicalGlobal.Restricts
   ⟨QRH.RepeatedMarks.Return.physicalB,QRH.RepeatedMarks.Return.physicalLambda,0,1/2,0,{sP}⟩
  constructor <;> norm_num [physicalGlobal,QRH.Record1252270103Return.globalFace,
   QRH.RepeatedMarks.Return.physicalB]""")
        sub1('exact ⟨mesh,hm,unit_source_restrict hr (unit_source_restrict physical_restricts hs)⟩',
             'exact ⟨mesh,hm,unit_source_restrict hr hs⟩')
    return text


def main():
    gen, out, capC, capP = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    sC = sys.argv[5] if len(sys.argv) > 5 else '11/250'
    sP = sys.argv[6] if len(sys.argv) > 6 else None
    transport = len(sys.argv) > 7 and sys.argv[7] == 'transport'
    phys, ft = set(), None
    if sP is not None and transport:
        import fork_transport as FT
        ft = FT.build_context()
        phys = {m[len('Record1252270103Return.'):] for m in ft['fork']}
    elif sP is not None:
        import fork_physical as FPH
        phys = {m[len('Record1252270103Return.'):] for m in FPH.forked_modules(FPH.all_modules())}
    fr = os.path.join(out, 'FinalReturn')
    os.makedirs(fr, exist_ok=True)
    texts = {m: open(f'{SRC}/Record1252270103Return/{m}.lean').read() for m in FORKED}
    fork_names = set()
    for m in FORKED:
        fork_names |= {n for n in declared(texts[m]) if n.startswith(NS_OLD + '.')}
    # Geometry.lean and TransportInstances.lean also declare Collet's generic class / intermediate
    # instance: only the final instances are re-instantiated.
    fork_names = {n for n in fork_names if n.split('.')[-1] not in ('Parameters', 'theta', 'ell', 'x', 'y',
                  'signalShift', 'signal', 'ell_pos', 'sixth_lt_ell', 'ell_lt_fifth', 'ell_lt_x', 'x_lt_y',
                  'y_lt_half', 'x_add_y', 'signal_at_boundary', 'intermediateBounds')}
    fin = finite_names()
    for m in FORKED:
        t = texts[m]
        body = t.split('\n', 1)[1] if t.startswith('/-') and t.split('\n', 1)[0].endswith('-/') else t
        if t.startswith('/-') and not t.split('\n', 1)[0].endswith('-/'):
            body = t[t.index('-/') + 3:]
        if m == 'Geometry':
            body = body[body.index('noncomputable def finalParameters'):]
            body = (f'import @@CPKG@@.Record1252270103Return.Geometry\nimport {PKG}.FinalReturn.ReturnConstants\n'
                    f'set_option autoImplicit false\nnamespace {NS_OLD}.Geometry\n' + body)
        if m == 'TransportInstances':
            body = re.sub(r'noncomputable def intermediateBounds.*?(?=end QRH)', '', body, flags=re.S)
            body = body.replace(f'#print axioms {NS_OLD}.Geometry.intermediateBounds\n', '')
            body = body.replace(f'import {CPKG}.Record1252270103Return.TransportGeometry',
                                f'import {CPKG}.Record1252270103Return.TransportGeometry\n'
                                f'import {PKG}.FinalReturn.Geometry')
        if m == 'CountWindows':
            head = body[:body.index('def returnWindow04')]
            tail = 'def returnBranches : List Branch := returnWindows.map ReturnCountWindow.toBranch\nend\nend ' + NS_OLD + '\n'
            parts = open(os.path.join(gen, 'FinalReturn', 'windows.lean.part')).read()
            nwin = len(re.findall(r'^def returnWindow\d+ ', parts, re.M))
            imps = ''.join(f'import {PKG}.FinalReturn.Rows.Admission{w:02d}\n' for w in range(1, nwin + 1))
            body = re.sub(r'(import [^\n]*CountingBridge\n)', r'\1' + imps, head) + parts + tail
        if m == 'FinalEdgeCertificates':
            head = body[:body.index('theorem window04_mem')]
            head = re.sub(r'import [^\n]*Record1252270103Finite\.Return\d+\n', '', head)
            edges = ['oldSmall', 'oldPeak', 'oldSwitch', 'newSwitch', 'newTop', 'newKink']
            imps = ''.join(f'import {PKG}.FinalReturn.Rows.Edge_{e}\n' for e in edges)
            head = re.sub(r'(import [^\n]*FinalEnvelopeBounds\n)', r'\1' + imps, head)
            parts = open(os.path.join(gen, 'FinalReturn', 'edges.lean.part')).read()
            body = head + parts + f'#print axioms {NS_OLD}.FinalEdges.closed_envelope_return_cover\n\nend\nend {NS_OLD}.FinalEdges\n'
        if m == 'SourceInlet':
            body = body.replace('def countGlobal : SourceFace := globalFace countCB countCL (549989/10000000)',
                                f'def countGlobal : SourceFace := globalFace countCB countCL ({capC})')
            body = body.replace('def physicalGlobal : SourceFace := globalFace physicalB physicalLambda (549989/10000000)',
                                f'def physicalGlobal : SourceFace := globalFace physicalB physicalLambda ({capP})')
            old_w = '⟨countCB-j/4000,countCL,2/5,11/25,17/500,11/250⟩'
            assert old_w in body
            body = body.replace(old_w, f'⟨countCB-j/4000,countCL,2/5,11/25,17/500,{sC}⟩')
            # the generic face constructors and restriction lemmas are Collet's own
            for nm in ('def globalFace', 'def broadFace', 'theorem global_restricts_broad',
                       'theorem unit_source_restrict', '/-- The scale is not specialized'):
                i = body.index(nm)
                j = body.find('\n\n', i)
                k = min(x for x in (body.find('\ndef ', i + 1), body.find('\ntheorem ', i + 1),
                                    body.find('\n/--', i + 1), body.find('\nend', i + 1)) if x > 0)
                body = body[:i] + body[k + 1:]
            body = body.replace(f'import {CPKG}.Record1252270103Finite.ReturnConstants',
                                f'import {CPKG}.Record1252270103Finite.ReturnConstants\n'
                                f'import @@CPKG@@.Record1252270103Return.SourceInlet')
        if m == 'WindowSources':
            body = body.replace(f'import {CPKG}.Record1252270103Return.CountSource',
                                f'import {CPKG}.Record1252270103Return.CountSource\n'
                                f'import {PKG}.FinalReturn.SourceInlet')
        if m == 'EndpointFromNumerator':
            body = strip_block(body, 'Intermediate')
        if m == 'EndpointFromSources':
            body = strip_block(body, 'Intermediate')
            body = body.replace(f'import {CPKG}.Record1252270103Return.EndpointFromNumerator',
                                f'import {CPKG}.Record1252270103Return.EndpointFromNumerator\n'
                                f'import @@CPKG@@.Record1252270103Return.EndpointFromSources')
        new = rewrite(body, fork_names, fin).replace('@@CPKG@@', CPKG)
        if sP is not None:
            new = lemma_d(m, new, phys, sP, capP, ft)

        write_if_changed(os.path.join(fr, f'{m}.lean'), HDR.format(m=m) + new)
    print('forked', len(FORKED), 'modules;', len(fork_names), 'qualified names re-pointed')


if __name__ == '__main__':
    main()
