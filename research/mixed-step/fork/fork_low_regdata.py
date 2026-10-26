import sys, re
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/mixed-step/fork')
from lowfork import *
M = 'Submissions.arvi_mixed_step.ForkMx.Record1252270103Source'
src = open(f'{CROOT}/Admission/SelectedRegularLowSourceData.lean').read()
first = src.split('\n', 1)[0]
i = src.index('theorem selected_nonfixed')
j = src.index('\nend\nend QRH.Record1252270103Source.Admission.SelectedRegularLowSource')
head = src[src.index('set_option autoImplicit false'):src.index('theorem sum_univ_subtype_filter')]
head = head.replace('local instance selectedRegularLowQuotientFinite', 'local instance selectedRegularLowQuotientFinite_mx')
p = Patch(src[i:j])
# selected_nonfixed over Selected_mx
p.R('''theorem selected_nonfixed {α Label Row:Type}[Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor α Z}{F:Family a Label}{rows:Finset Row}{second:Bool}
    (G:Selected F Row rows second)''', '''theorem selected_nonfixed_mx {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor_mx α₀ α Z}{F:Family_mx a Label}{rows:Finset Row}{second:Bool}
    (G:Selected_mx F Row rows second)''')
p.R('local instance regularLowPointwiseDecEq', 'local instance regularLowPointwiseDecEq_mx')
p.R('theorem apply_actual_family (hcall:', 'theorem apply_actual_family_mx (hcall:')
# the two s binders (hcall and conclusion)
p.R('''    ∀(reflected second : Bool)(s : Input α)(Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ)),R₀≠0 →''',
    '''    ∀(reflected second : Bool){α₀ : Type}[Fintype α₀][DecidableEq α₀](s₀ : Input α₀)(s : Input α)
      (Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ)),R₀≠0 →''')
p.R('''    ∀(reflected second : Bool)(s : Input α)(Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ))(hR₀:R₀≠0)(hseed:Squarefree seed)(hZanchor:1<Z),''',
    '''    ∀(reflected second : Bool){α₀ : Type}[Fintype α₀][DecidableEq α₀](s₀ : Input α₀)(s : Input α)
      (Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ))(hR₀:R₀≠0)(hseed:Squarefree seed)(hZanchor:1<Z),''')
p.R('      s.η=ηanchor →', '      s₀.η=ηanchor →', 2)
p.R('fixedParentUnit left s.η l:O)', 'fixedParentUnit left s₀.η l:O)', 2)
p.sub(r'(?<![A-Za-z_0-9.₀])s modifier\b', 's₀ modifier')
p.R('geometryRawFixedMask s R₀', 'geometryRawFixedMask s₀ R₀', 4)
p.R('((actualAllocations s.pools (if reflected', '((actualAllocations s₀.pools (if reflected', 2)
p.R('''CoupledFirst.balancedColumnScalar reflected s₀ modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s)) hK bin''', '''CoupledFirst.balancedColumnScalar reflected s₀ modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s₀)) hK bin''', 2)
p.R('''    ∀(P:Finset (Ideal O))(poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z (sourceAReal n low bcell) ell poolMesh poolLoss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*sourceAReal n low bcell ∧ mainRadius l+6*sourceAReal n low bcell≤radiusMax) →''',
    '''    ∀(P:Finset (Ideal O))(poolAmp poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z poolAmp ell poolMesh poolLoss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*poolAmp ∧ mainRadius l+6*poolAmp≤radiusMax) →''', 2)
p.R('''        ((mainRadius l+6*sourceAReal n low bcell)/ell);''', '''        ((mainRadius l+6*poolAmp)/ell);''', 2)
p.R('''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →''',
    '''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →
    s₀.W₁=(p.profile 0:ℝ→ℂ) → s₀.W₂=(p.profile 1:ℝ→ℂ) → Fintype.card α₀≤N → 1≤s₀.lower →
    CenteredMomentOriginalCommonHarmonic.sourceRadius s₀≤Z^Bmass →''', 2)
p.R('''    (∀l,omega l≤''', '''    ∀κ:ℝ,sourceAReal n low bcell-poolAmp≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ →
    (∀l,φ≤(∑i,w i)-∑i∈liveIndices (sel l).B₁.val,w i) →
    (∀l,omega l≤''', 2)
p.R('Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+', 'Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+κ+Bmass*εmass+', 2)
# conclusion: plain zeros of both parents and the two-parent anchor
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
p.R('''variable {n low:Source}{bcell εsource mesh B loss εmask q:ℝ}''', '''variable {n low:Source}{bcell φ εsource mesh B loss εmask q:ℝ}''')
# proof
p.R('''  intro T reflected second s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hseed hZanchor hanchor
    K modifier left unit reserveGeom manchor hm hml hm2 hz₁ hz₂ anchor''', '''  intro T reflected second α₀ _ _ s₀ s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hseed hZanchor hanchor
    K modifier left unit reserveGeom manchor hm hml hm2 hz₁₀ hz₂₀ hz₁ hz₂ anchor''')
p.R('''    hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hsourceRadius ht''',
    '''    hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hsourceRadius hW₁₀ hW₂₀ hN₀ hslower₀ hsourceRadius₀ ht''')
p.R('''    hradiusMax hradial hraw P poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ extra hphase''', '''    hradiusMax hradial hraw P poolAmp poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ extra κ hshift hφ hphase''')
p.R('''  have hs:=hcall T reflected second s Am₁''', '''  have hs:=hcall T reflected second s₀ s Am₁''')
p.R('''    (fun l hn=>selected_nonfixed G hm hml hm2 hQ72 (inc l)''', '''    (fun l hn=>selected_nonfixed_mx G hm hml hm2 hQ72 (inc l)''')
p.R('''  have hs₄:=hs₃ hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hseed hsourceRadius (fun l=>(G.datum (inc l)).hC) ht''',
    '''  have hs₄:=hs₃ hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hseed hsourceRadius
    hW₁₀ hW₂₀ hN₀ hslower₀ hsourceRadius₀ (fun l=>(G.datum (inc l)).hC) ht''')
p.R('''    hradiusMax hradial hraw hmissingx P poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ hphase''', '''    hradiusMax hradial hraw hmissingx P poolAmp poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ κ hshift hφ hphase''')
hdr = first + '''
Mixed step (L4/L5, F3): fork of Record1252270103Source.Admission.SelectedRegularLowSourceData;
changes: two parents, two amplitudes (as in SelectedLowSource_mx). The conclusion is stated for
`Anchor_mx`/`Family_mx`/`Selected_mx` built from the first layer `s₀` and the second-layer parent `s`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularLowSourceData
import ''' + M + '''.Admission.SelectedRegularSourceData
'''
out = hdr + head + p.d + '\nend\nend QRH.Record1252270103Source.Admission.SelectedRegularLowSource\n#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowSource.selected_nonfixed_mx\n#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowSource.apply_actual_family_mx\n'
open(f'{OROOT}/Admission/SelectedRegularLowSourceData.lean', 'w').write(out)
print('ok')
