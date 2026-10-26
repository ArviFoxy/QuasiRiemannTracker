import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/mixed-step/fork')
from lowfork import *
M = 'Submissions.arvi_mixed_step.ForkMx.Record1252270103Source'
def edit(p):
    split_statement(p, 'global_selected_low_positive_family_missing_bins')
    p.R('''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowSourceReindex.global_selected_low_positive_family_injective
    Kgraph n low bcell εsource hg hn hlow ha hq0 hq1 hG hεsource''',
        '''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowSourceReindex.global_selected_low_positive_family_injective_mx
    n low bcell φ εsource hprice hlow ha hq0 hq1 hG hεsource''')
    split_intro(p)
    p.R('''      forcedProfileCost s*(max 1 (forcedProfileCost s))^2)*Cslot^N*
    Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+cellWidth+missingWidth+εmask*(Bmissing+missingWidth)+''',
        '''      forcedProfileCost s*(max 1 (forcedProfileCost s))^2)*Cslot^N*
    Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+κ+Bmass*εmass+cellWidth+missingWidth+εmask*(Bmissing+missingWidth)+''')
    p.R('    have hs:=hZ.2 T reflected second s Am₁', '    have hs:=hZ.2 T reflected second s₀ s Am₁')
    p.R('''      hseed hsourceRadius (fun r=>hC₂ (inc r))''', '''      hseed hsourceRadius hW₁₀ hW₂₀ hN₀ hslower₀ hsourceRadius₀ (fun r=>hC₂ (inc r))''')
    p.R('''      P poolMesh BD Bsource depth (fun r=>H0 (inc r))''', '''      P poolAmp poolMesh BD Bsource depth (fun r=>H0 (inc r))''')
    p.R('''      (fun r=>hcommon₂ (inc r)) (fun r=>hphase (inc r))''',
        '''      (fun r=>hcommon₂ (inc r)) κ hshift (fun r=>hφ (inc r)) (fun r=>hphase (inc r))''')
fork_module('Admission/SelectedLowSourceMissingBins', ['global_selected_low_positive_family_missing_bins'],
  'Mixed step (L4/L5, F3): fork of Record1252270103Source.Admission.SelectedLowSourceMissingBins; changes:\ntwo parents, two amplitudes, node price as a hypothesis (as in SelectedLowSource_mx).',
  [M + '.Admission.SelectedLowSourceReindex'], edit)
