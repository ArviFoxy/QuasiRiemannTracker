"""Fork the window-dependent tail of arvi_density's Return/ into Submissions/arvi_return_tuning/.

Forks live in namespace QRH.ArviDensity.Return.Tuning (a sub-namespace of the original, so that names
resolve exactly as in the originals, while the full names differ). Each fork keeps its notices and gets
one 'Modified by ArviFoxy' line.
"""
SRC = '/home/user/lean-env/qrh/Submissions/arvi_density/Return/'
DST = '/home/user/lean-env/qrh/Submissions/arvi_return_tuning/'
NOTE = ('/- Modified by ArviFoxy (2026-10-29): forked into Submissions.arvi_return_tuning, namespace '
        'QRH.ArviDensity.Return.Tuning, over the reflective windows and edge covers of this package '
        '(`w.toAdmitted` written as `ReturnCountWindow.toAdmitted w`). -/')
NS_OLD = 'namespace QRH.ArviDensity.Return\nopen QRH.Record1252270103Return'
NS_NEW = 'namespace QRH.ArviDensity.Return.Tuning\nopen QRH.Record1252270103Return QRH.ArviReturnTuning'
IMPORTS = {
    'Submissions.arvi_density.Return.Windows': 'Submissions.arvi_return_tuning.Windows',
    'Submissions.arvi_density.Return.FinalWindows': 'Submissions.arvi_return_tuning.FinalWindows',
    'Submissions.arvi_density.Return.FinalScheme': 'Submissions.arvi_return_tuning.FinalScheme',
    'Submissions.arvi_density.Return.FinalEnvelopeBounds': 'Submissions.arvi_return_tuning.FinalEnvelopeBounds',
    'Submissions.arvi_density.Return.EdgeCertificates': 'Submissions.arvi_return_tuning.EdgeCertificates',
    'Submissions.arvi_density.Return.FinalRows': 'Submissions.arvi_return_tuning.FinalRows',
    'Submissions.arvi_density.Return.FinalSchedule': 'Submissions.arvi_return_tuning.FinalSchedule',
    'Submissions.arvi_density.Return.EndpointFromSources': 'Submissions.arvi_return_tuning.EndpointFromSources',
}


def last_notice_end(s):
    """index just after the last leading comment block"""
    i = 0
    while True:
        j = s.find('/-', i)
        if j != i:
            return i
        k = s.find('-/', j) + 2
        i = k + 1 if s[k:k + 1] == '\n' else k


def fork(name, extra=()):
    s = open(SRC + name).read()
    k = last_notice_end(s)
    s = s[:k] + NOTE + '\n' + s[k:]
    for a, b in IMPORTS.items():
        s = s.replace('import ' + a + '\n', 'import ' + b + '\n')
    for a, b in extra:
        assert a in s, (name, a)
        s = s.replace(a, b)
    assert 'Submissions.arvi_density.Return.Windows' not in s
    open(DST + name, 'w').write(s)


fork('FinalWindows.lean', [(NS_OLD, NS_NEW), ('end QRH.ArviDensity.Return', 'end QRH.ArviDensity.Return.Tuning'),
                           ('returnWindows.map ReturnCountWindow.toAdmitted', 'returnWindows.map ReturnCountWindow.toAdmitted')])
fork('FinalScheme.lean', [(NS_OLD, NS_NEW), ('end QRH.ArviDensity.Return', 'end QRH.ArviDensity.Return.Tuning'),
                          ('w.toAdmitted.face=countingSource w.branch', '(ReturnCountWindow.toAdmitted w).face=countingSource w.branch')])
fork('FinalEnvelopeBounds.lean', [
    ('namespace QRH.ArviDensity.Return.FinalEdges\nopen QRH.Record1252270103Return',
     'namespace QRH.ArviDensity.Return.Tuning.FinalEdges\nopen QRH.Record1252270103Return QRH.ArviReturnTuning'),
    ('end QRH.ArviDensity.Return.FinalEdges', 'end QRH.ArviDensity.Return.Tuning.FinalEdges'),
    ('w.toAdmitted∈finalCountScheme.windows', 'ReturnCountWindow.toAdmitted w∈finalCountScheme.windows'),
    ('change w.toAdmitted∈returnWindows.map', 'change ReturnCountWindow.toAdmitted w∈returnWindows.map'),
    ('w.toAdmitted.toBranch∈', '(ReturnCountWindow.toAdmitted w).toBranch∈'),
    ('⟨w.toAdmitted,hw\',rfl⟩', '⟨ReturnCountWindow.toAdmitted w,hw\',rfl⟩'),
    ('w.toAdmitted.toBranch.available δ p', '(ReturnCountWindow.toAdmitted w).toBranch.available δ p')])
fork('FinalRows.lean', [(NS_OLD, NS_NEW), ('end QRH.ArviDensity.Return', 'end QRH.ArviDensity.Return.Tuning')])
fork('FinalSchedule.lean', [
    ('namespace QRH.ArviDensity.Return\nopen QRH.Record1252270103Return', 'namespace QRH.ArviDensity.Return.Tuning\nopen QRH.Record1252270103Return'),
    ('end QRH.ArviDensity.Return', 'end QRH.ArviDensity.Return.Tuning'),
    ('QRH.ArviDensity.Return.finalCountScheme', 'QRH.ArviDensity.Return.Tuning.finalCountScheme'),
    ('QRH.ArviDensity.Return.final_old_rows', 'QRH.ArviDensity.Return.Tuning.final_old_rows'),
    ('QRH.ArviDensity.Return.final_new_rows', 'QRH.ArviDensity.Return.Tuning.final_new_rows')])
fork('EndpointFromSources.lean', [(NS_OLD, NS_NEW), ('end QRH.ArviDensity.Return', 'end QRH.ArviDensity.Return.Tuning'),
                                  ('namespace Final\n', 'namespace Final\nopen QRH.ArviDensity.Return.Final\n')])
fork('Endpoint.lean', [(NS_OLD, NS_NEW), ('end QRH.ArviDensity.Return', 'end QRH.ArviDensity.Return.Tuning')])
print('forked')
