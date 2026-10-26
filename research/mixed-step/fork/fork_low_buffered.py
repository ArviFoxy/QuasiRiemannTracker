import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/mixed-step/fork')
from lowfork import *
M = 'Submissions.arvi_mixed_step.ForkMx.Record1252270103Source'
def edit(p):
    split_statement(p, 'global_selected_low_buffered_positive_family')
    p.R('''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowSourceMissingBins.global_selected_low_positive_family_missing_bins
    Kgraph n low bcell εsource hg hn hlow ha hq0 hq1 hG hεsource''',
        '''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowSourceMissingBins.global_selected_low_positive_family_missing_bins_mx
    n low bcell φ εsource hprice hlow ha hq0 hq1 hG hεsource''')
    split_intro(p)
    p.R('  have hs:=hZ.2 T reflected second s Am₁', '  have hs:=hZ.2 T reflected second s₀ s Am₁')
    p.R('''    hseed hsourceRadius (fun l=>hC₂ (inc l))''', '''    hseed hsourceRadius hW₁₀ hW₂₀ hN₀ hslower₀ hsourceRadius₀ (fun l=>hC₂ (inc l))''')
    p.R('''    P poolMesh BD Bsource depth (fun l=>H0 (inc l))''', '''    P poolAmp poolMesh BD Bsource depth (fun l=>H0 (inc l))''')
    p.R('''    (fun l=>hcommon₂ (inc l)) (fun l=>hphase (inc l))''',
        '''    (fun l=>hcommon₂ (inc l)) κ hshift (fun l=>hφ (inc l)) (fun l=>hphase (inc l))''')
fork_module('Admission/SelectedLowBufferedSource', ['global_selected_low_buffered_positive_family'],
  'Mixed step (L4/L5, F3): fork of Record1252270103Source.Admission.SelectedLowBufferedSource; changes:\ntwo parents, two amplitudes, node price as a hypothesis (as in SelectedLowSource_mx).',
  [M + '.Admission.SelectedLowSourceMissingBins'], edit)
