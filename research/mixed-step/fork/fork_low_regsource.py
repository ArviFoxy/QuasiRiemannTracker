import sys, re
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/mixed-step/fork')
from lowfork import *
M = 'Submissions.arvi_mixed_step.ForkMx.Record1252270103Source'
def edit(p):
    p.sub(r'theorem global_selected_regular_low_buffered_positive_family \(Kgraph:ℚ\)\(n low:Source\)\(bcell εsource:ℝ\)\n    \(hg:RealGeometry Kgraph n low bcell\)\(hn:ParentGood n\)\(hlow:ParentGood low\)',
          'theorem global_selected_regular_low_buffered_positive_family_mx (n low:Source)(bcell φ εsource:ℝ)\n    (hprice:QRH.MixedStep.Ledger.MixedNodePrice n low bcell φ)(hlow:ParentGood low)')
    p.R('''    ∀(reflected second : Bool)(s : Input α)(Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ))(hR₀:R₀≠0)(hseed:Squarefree seed)(hZanchor:1<Z),''',
        '''    ∀(reflected second : Bool){α₀ : Type}[Fintype α₀][DecidableEq α₀](s₀ : Input α₀)(s : Input α)
      (Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ))(hR₀:R₀≠0)(hseed:Squarefree seed)(hZanchor:1<Z),''')
    p.R('      s.η=ηanchor →', '      s₀.η=ηanchor →')
    p.R('fixedParentUnit left s.η l:O)', 'fixedParentUnit left s₀.η l:O)')
    p.sub(r'(?<![A-Za-z_0-9.₀])s modifier\b', 's₀ modifier')
    p.R('geometryRawFixedMask s R₀', 'geometryRawFixedMask s₀ R₀', 2)
    p.R('((actualAllocations s.pools (if reflected', '((actualAllocations s₀.pools (if reflected')
    p.R('''CoupledFirst.balancedColumnScalar reflected s₀ modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s)) hK bin''', '''CoupledFirst.balancedColumnScalar reflected s₀ modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s₀)) hK bin''')
    p.R('''    ∀(P:Finset (Ideal O))(poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z (sourceAReal n low bcell) ell poolMesh poolLoss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*sourceAReal n low bcell ∧ mainRadius l+6*sourceAReal n low bcell≤radiusMax) →''',
    '''    ∀(P:Finset (Ideal O))(poolAmp poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z poolAmp ell poolMesh poolLoss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*poolAmp ∧ mainRadius l+6*poolAmp≤radiusMax) →''')
    p.R('''        ((mainRadius l+6*sourceAReal n low bcell)/ell);''', '''        ((mainRadius l+6*poolAmp)/ell);''')
    p.R('''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →''',
        '''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →
    s₀.W₁=(p.profile 0:ℝ→ℂ) → s₀.W₂=(p.profile 1:ℝ→ℂ) → Fintype.card α₀≤N → 1≤s₀.lower →
    CenteredMomentOriginalCommonHarmonic.sourceRadius s₀≤Z^Bmass →''')
    p.R('''    (∀l,omega l≤''', '''    ∀κ:ℝ,sourceAReal n low bcell-poolAmp≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ →
    (∀l,φ≤(∑i,w i)-∑i∈liveIndices (sel l).B₁.val,w i) →
    (∀l,omega l≤''')
    p.R1('Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+', 'Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+κ+Bmass*εmass+')
    p.R('''(hm2:(2:O)∣manchor)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0),
    let anchor : Anchor α Z := {
      s := s
      modifier := modifier''', '''(hm2:(2:O)∣manchor)(hz₁₀:s₀.W₁ 0=0)(hz₂₀:s₀.W₂ 0=0)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0),
    let anchor : Anchor_mx α₀ α Z := {
      s₀ := s₀
      modifier₀ := modifier
      s := s''')
    p.R('''      seed_sf := hseed
      zero₁ := hz₁''', '''      seed_sf := hseed
      zero₁₀ := hz₁₀
      zero₂₀ := hz₂₀
      zero₁ := hz₁''')
    p.R('''    ∀{Label:Type}[Fintype Label](F:Family anchor Label),
    ∀{Row:Type}(rows:Finset Row)(G:Selected F Row rows second),''', '''    ∀{Label:Type}[Fintype Label](F:Family_mx anchor Label),
    ∀{Row:Type}(rows:Finset Row)(G:Selected_mx F Row rows second),''')
    p.R('''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowBufferedSource.global_selected_low_buffered_positive_family
    Kgraph n low bcell εsource hg hn hlow ha hqhalf hq1 hG hεsource''', '''  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowBufferedSource.global_selected_low_buffered_positive_family_mx
    n low bcell φ εsource hprice hlow ha hqhalf hq1 hG hεsource''')
    p.R('  exact apply_actual_family (hQ72:=hQ72) (hQray:=hQray) hZ.2', '  exact apply_actual_family_mx (hQ72:=hQ72) (hQray:=hQray) hZ.2')
fork_module('Admission/SelectedRegularLowSource', ['global_selected_regular_low_buffered_positive_family'],
  'Mixed step (L4/L5, F3): fork of Record1252270103Source.Admission.SelectedRegularLowSource; changes:\ntwo parents, two amplitudes, node price as a hypothesis (as in SelectedLowSource_mx).',
  [M + '.Admission.SelectedLowBufferedSource', M + '.Admission.SelectedRegularLowSourceData'], edit)
