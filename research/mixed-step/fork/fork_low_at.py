import sys, re
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/mixed-step/fork')
from lowfork import *
M = 'Submissions.arvi_mixed_step.ForkMx.Record1252270103Source'
def edit(p):
    p.R('def RegularLowAt {α:Type}[Fintype α]', 'def RegularLowAt_mx {α:Type}[Fintype α]')
    p.R('    (n low:Source)(bcell θloss mesh εslot τsource:ℝ)(N:ℕ)', '    (n low:Source)(bcell φ ellPool θloss mesh εslot τsource:ℝ)(N:ℕ)')
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
    p.R('''        ∀(P:Finset (Ideal O))(poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z (sourceAReal n low bcell) (sourceAReal n low bcell/2) poolMesh θloss BD Bsource depth →''',
        '''        ∀(P:Finset (Ideal O))(poolAmp poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z poolAmp ellPool poolMesh θloss BD Bsource depth →''')
    p.R('''      (∀l,0≤mainRadius l+6*sourceAReal n low bcell ∧ mainRadius l+6*sourceAReal n low bcell≤32) →''',
        '''      (∀l,0≤mainRadius l+6*poolAmp ∧ mainRadius l+6*poolAmp≤32) →''')
    p.R('''        ((mainRadius l+6*sourceAReal n low bcell)/(sourceAReal n low bcell/2));''',
        '''        ((mainRadius l+6*poolAmp)/ellPool);''')
    p.R('''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^(6:ℝ) →''',
        '''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^(6:ℝ) →
    s₀.W₁=(p.profile 0:ℝ→ℂ) → s₀.W₂=(p.profile 1:ℝ→ℂ) → Fintype.card α₀≤N → 1≤s₀.lower →
    CenteredMomentOriginalCommonHarmonic.sourceRadius s₀≤Z^(6:ℝ) →''')
    p.R('''    (∀l,omega l≤''', '''    ∀κ:ℝ,sourceAReal n low bcell-poolAmp≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ →
    (∀l,φ≤(∑i,w i)-∑i∈liveIndices (sel l).B₁.val,w i) →
    (∀l,omega l≤''')
    p.R('''        Z^(-8*(n.allowance:ℝ)+θloss+θloss+6*(θloss/100)+θloss+θloss+(θloss/100)*(6+θloss)+''',
        '''        Z^(-8*(n.allowance:ℝ)+θloss+θloss+κ+6*(θloss/100)+θloss+θloss+(θloss/100)*(6+θloss)+''')
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
    # controls
    p.R('''theorem regular_low_controls (Kgraph:ℚ)(n low:Source)(bcell θloss:ℝ)
    (hg:RealGeometry Kgraph n low bcell)(hn:ParentGood n)(hlow:ParentGood low)''',
        '''theorem regular_low_controls_mx (n low:Source)(bcell φ ellPool θloss:ℝ)
    (hprice:QRH.MixedStep.Ledger.MixedNodePrice n low bcell φ)(hlow:ParentGood low)(hellPool:0<ellPool)''')
    p.R('''    (hmesh:mesh≤regularLowMesh Kgraph n low bcell θloss hg hn hlow ha hqhalf hq1 hG hθ)''',
        '''    (hmesh:mesh≤regularLowMesh_mx n low bcell φ θloss hprice hlow ha hqhalf hq1 hG hθ)''')
    p.R('''      RegularLowAt rayModulus Hray hH n low bcell θloss mesh εslot τsource N Mslot W ηanchor η₀ Q hQray''',
        '''      RegularLowAt_mx rayModulus Hray hH n low bcell φ ellPool θloss mesh εslot τsource N Mslot W ηanchor η₀ Q hQray''')
    p.R('''  obtain ⟨Cslot,hCslot,hslots⟩:=regular_low_slot_supply Kgraph n low bcell θloss hg hn hlow ha hqhalf hq1 hG hθ''',
        '''  obtain ⟨Cslot,hCslot,hslots⟩:=regular_low_slot_supply_mx n low bcell φ θloss hprice hlow ha hqhalf hq1 hG hθ''')
    p.R('''    2 2 θloss (sourceAReal n low bcell/2) (lowerFactor N 1 (1/4)) 32 θloss 6 (θloss/100) θloss
    (by norm_num) (by norm_num) hθ (div_pos hg.a_pos (by norm_num))''',
        '''    2 2 θloss ellPool (lowerFactor N 1 (1/4)) 32 θloss 6 (θloss/100) θloss
    (by norm_num) (by norm_num) hθ hellPool''')
    p.R('''  unfold RegularLowAt
''', '''  unfold RegularLowAt_mx
''')
fork_module('High/GlobalPhysicalRegularLowAt', ['RegularLowAt', 'regular_low_controls'],
  '''Mixed step (L4/L5, F3): fork of Record1252270103Source.High.GlobalPhysicalRegularLowAt; changes:
two parents, two amplitudes, node price as a hypothesis.
`RegularLowAt_mx … n low bcell φ ellPool θloss …`: the anchor is `Anchor_mx` (first layer `s₀`,
second-layer parent `s`); the pool is the actual one, `FixedCellPoolData P Z poolAmp ellPool` with the
pool width `poolAmp` quantified with the pool and `ellPool` fixed (`ellPool = poolAmp/2` at the call);
the amplitude `sourceAReal n low bcell` (the virtual `a_v` at a virtual node) stays the radius and
coordinate amplitude; `∀ κ, hshift → … Z^(… + κ)`; the frozen-width margin `φ` per label.
`regular_low_controls_mx` needs only `MixedNodePrice n low bcell φ`, `ParentGood low` and
`0 < ellPool` (no node geometry: Collet used `RealGeometry` only for `0 < sourceAReal/2`, the pool's
`ell`).''',
  [M + '.High.GlobalPhysicalRegularLowParameters', M + '.Admission.SelectedRegularSourceData'], edit)
