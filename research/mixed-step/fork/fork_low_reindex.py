import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/mixed-step/fork')
from lowfork import *
M = 'Submissions.arvi_mixed_step.ForkMx.Record1252270103Source'
def edit(p):
    split_statement(p, 'global_selected_low_positive_family_injective')
    p.R('''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowSource.global_selected_low_positive_family
    Kgraph n low bcell εsource hg hn hlow ha hq0 hq1 hG hεsource''',
        '''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowSource.global_selected_low_positive_family_mx
    n low bcell φ εsource hprice hlow ha hq0 hq1 hG hεsource''')
    split_intro(p)
    p.R('  have hs:=hZ.2 T reflected second s Am₁', '  have hs:=hZ.2 T reflected second s₀ s Am₁')
    p.R('''    hseed hsourceRadius (fun j=>hC₂ (back j))''', '''    hseed hsourceRadius hW₁₀ hW₂₀ hN₀ hslower₀ hsourceRadius₀ (fun j=>hC₂ (back j))''')
    p.R('''    P poolMesh BD Bsource depth (fun j=>H0 (back j))''', '''    P poolAmp poolMesh BD Bsource depth (fun j=>H0 (back j))''')
    p.R('''    (fun j=>hcommon₂ (back j)) (fun j=>hphase (back j))''',
        '''    (fun j=>hcommon₂ (back j)) κ hshift (fun j=>hφ (back j)) (fun j=>hphase (back j))''')
fork_module('Admission/SelectedLowSourceReindex', ['global_selected_low_positive_family_injective'],
  'Mixed step (L4/L5, F3): fork of Record1252270103Source.Admission.SelectedLowSourceReindex; changes:\ntwo parents, two amplitudes, node price as a hypothesis (as in SelectedLowSource_mx).',
  [M + '.Admission.SelectedLowSource'], edit)
