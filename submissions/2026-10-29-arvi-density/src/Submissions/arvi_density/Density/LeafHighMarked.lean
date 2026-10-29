/- The marked HIGH class sum of the density-split leaf.

For a buffered bin `c` (height index `i`, value `a = bufferValue e c`, density `ν = 2a-1`), the kept
HIGH rows of the packed natural state that have bin `c` form a set of nonzero frequencies of the
whole-source family of the fixed anchor dictionary, with exactly the zero guards of
`RetainedZeroBin` at the base height `Z^τ`. PR 76's dictionary count
`actual_dictionary_regular_raw_max_uniform_tau_rm` sums the squared slot products of the regular
rows (cores outside the finite exceptional set) with the repeated-mark gain:

  `∑_rows (∏_slots max 1 ‖slot‖)² ≤ C·Z^{τJ}·Z^{ρ(ν) F + ν S - gainC ν B₀ L₀ c₀ S F + loss}`

(`high_class_sum_marked`). The exceptional rows are counted by Collet's `finite_core_raw_count`
(`high_exceptional_count`, `≤ Cex·H^{1/6}`). The moments of the count are produced inside the pivot
from the parent source `UnitFaceSource ⟨B₀,L₀,0,B₀,0,c₀⟩` alone; the numerical side conditions are
bundled in `PivotParams`. -/
import Submissions.arvi_density.Density.HighParams
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.PositiveRadius.SomeDictionary
import Submissions.hailey_collet_1252270103.Record12518109Gain.ExceptionalCounts
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularPositiveRawNatural
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularRetainedNaturalBins

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.ArviDensity.Density
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedProfile
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open LocalMoment HeckeDetectorZeros ProbePhysical
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open Record12518109Natural Record12518109GainWholeGeometry Record12518109GainExceptional
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem unmarkedDensity_le_one' {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 3/4) : unmarkedDensity ν ≤ 1 := by
  unfold unmarkedDensity
  have : 0 ≤ 10*ν/(3*(5-2*ν)) := div_nonneg (by linarith) (by nlinarith)
  linarith

theorem high_rho_eq (ν : ℝ) : QRH.Record1252270103Source.High.rho ν = unmarkedDensity ν :=
  (QRH.Record1252270103Source.High.rho_eq_original ν).trans rfl

section
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- **The pivot on raw rows** (`Row = NonzeroFrequency`, unit puncture): PR 76's dictionary count
with the side conditions bundled in `PivotParams`. -/
theorem high_dictionary_sum_marked {Index : Type} [Fintype Index] [Nonempty Index]
    (base : Index → Character) (η₀ : Character) (B₀ L₀ c₀ sourceMesh : ℝ)
    (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1) (hL : 1 < L₀) (hc0 : 0 ≤ c₀) (hc1 : c₀ < 1)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (PP : PivotParams sourceMesh)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource
      ⟨B₀, L₀, 0, B₀, 0, c₀⟩ sourceMesh PP.εm) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ < PP.dmin/2 → 4*τ < PP.dmin*PP.ηw →
      2*τ < PP.dmin*PP.ηslot → ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (index : Index) (F a : ℝ) (i : ℕ), i ≤ PP.I → 3/4 ≤ a → a ≤ 7/8 → PP.qlo ≤ F →
      F ≤ PP.Q → PP.binWidth ≤ (2*a-1)/2 →
      ∀ (rows : Finset NonzeroFrequency) (slots : Finset Slot) (w σ v : Slot → ℝ) (t : ℝ)
        (θ : Slot → RayQuotient.Characters M H) (χ : NonzeroFrequency → Character),
      (∀ u ∈ rows, rawFrequencyNorm u ≤ Z^F) →
      (∀ u ∈ rows, ¬ (wholeRegularDictionary M H hH (base index) η₀).exceptionalCore
        (sixthFrequencyEquiv.symm u).1) →
      (∀ u ∈ rows, ∀ K, idealCoeff (χ u) K = idealCoeff
        (excluded (naturalRow (base index) u.val u.property).character 1) K) →
      ∀ hn : (∀ u ∈ rows, ∀ j, (wholeSourceFamily M H hH η₀ (χ u) j).residue ≠ 1),
      (∀ u ∈ rows, ∀ hh : u ∈ rows, zeroMaximum (wholeSourceFamily M H hH η₀ (χ u)) (hn u hh)
        (3*(i+1:ℕ)*Z^τ) < a + 2*PP.e) →
      (∀ u ∈ rows, ∀ hh : u ∈ rows, a ≤ zeroMaximum (wholeSourceFamily M H hH η₀ (χ u))
        (hn u hh) ((3*i:ℕ)*Z^τ)) →
      (∀ s ∈ slots, PP.wmin ≤ w s) → (∀ s ∈ slots, (33/50:ℝ) ≤ σ s) →
      (∀ s ∈ slots, σ s ≤ 33/50) → (∀ s ∈ slots, w s ≤ PP.mesh * PP.dmin) →
      |t| + Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ → (∀ s ∈ slots, |t + v s| + Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ) →
      ∑ u ∈ rows, (∏ s ∈ slots, max 1 ‖WeightedHigh.labeledRawSlot M H hH η₀ W Z w σ v
          (fun _ : NonzeroFrequency => t) θ χ u s‖)^2 ≤
        C * (1 + rawGeometryHeight Z τ PP.I)^J *
          Z^(unmarkedDensity (2*a-1) * F + (2*a-1) * ∑ s ∈ slots, w s -
            QRH.RepeatedMarks.Source.gainC (2*a-1) B₀ L₀ c₀ (∑ s ∈ slots, w s) F +
            PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (2*a-1)*PP.ζ + PP.η) +
            unmarkedDensity (2*a-1) * PP.δ + 2*PP.binWidth*∑ s ∈ slots, w s) := by
  obtain ⟨bRad₀, hbRad₀, hsRad⟩ :=
    CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  have hbRad : 2 ≤ max 2 bRad₀ := le_max_left _ _
  have hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant : ℝ → ℂ) ⊆
      Set.Iic (max 2 bRad₀) := fun x hx =>
    (show x ≤ bRad₀ from hsRad hx).trans (le_max_right 2 bRad₀)
  obtain ⟨J, C, hC, hpiv⟩ :=
    QRH.Record1252270103Source.PositiveRadius.Some.actual_dictionary_regular_raw_max_uniform_tau_rm
      (Slot := Slot) M H hH base η₀ B₀ L₀ c₀ sourceMesh hB0 hB1 hL hc0 hc1
      canonicalDensityCountingSetup W (max 2 bRad₀) PP.εm PP.binWidth PP.ζ PP.η PP.dmin PP.dmax
      PP.rmin PP.Rwidth PP.εp PP.e PP.κ PP.ηw PP.εslot PP.ηslot PP.I PP.δ PP.Bmask PP.Broot
      PP.wmin PP.hδ PP.hBmask PP.hBroot PP.hwmin hparentSource hWs hW hbRad hrad PP.hbin PP.hη
      PP.hζ PP.hεm PP.hdmin PP.hdmax PP.hrmin PP.hRw PP.hε PP.hεsmall PP.he PP.he' PP.hκ PP.hκ'
      PP.hηw PP.hbudget PP.hεslot PP.hηslot PP.hslotBudget PP.hgap hβ PP.qlo PP.Q PP.mesh PP.hqlo
      PP.hQ PP.hQroot PP.hdlo PP.hdsource PP.hrlower PP.hmesh PP.hmeshmax PP.hmeshR
  refine ⟨J, C, hC, ?_⟩
  intro τ hτ h1 h2 h3
  filter_upwards [hpiv τ hτ h1 h2 h3] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro index F a i hi ha ha' hF hF' hbin rows slots w σ v t θ χ hnorm hreg hcoeff hn hup hlow hw
    hσ hσ' hwm hwin hwin'
  have hne : Nonempty NonzeroFrequency := ⟨⟨1, one_ne_zero⟩⟩
  have key := hZ.2 index F a i hi ha ha' hF hF' hbin (Row := NonzeroFrequency) rows id
    (fun _ _ _ _ h => h) slots w σ v (fun _ => t) θ (fun _ => 1) χ hnorm hreg
    (fun _ _ => one_ne_zero)
    (fun _ _ => by simpa using Real.one_le_rpow hZ.1.le PP.hBmask) hcoeff hn hup hlow hw hσ hσ'
    hwm (fun _ _ => hwin) (fun _ _ s hs => hwin' s hs)
  simpa only [high_rho_eq] using key

end

section
variable (rayM : Ideal O) [NeZero rayM]
local instance leafHighMarkedQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **Marked HIGH class sum.** Constants `J`, `C` first (after the parameters), then the height
scale `τ` (below `dmin/2`, `dmin·ηw/4`, `dmin·ηslot/2`), then the threshold in `Z`; then the
anchor, the state (character an anchor, unit puncture), the bin `c`, the row-width bound `F`, a
finite set of regular rows of the bin with `N(z) ≤ Z^F`, and slot data with widths in
`[wmin, mesh·dmin]` inside the height window. -/
theorem high_class_sum_marked {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {κ : Type} [Fintype κ] [Nonempty κ] (anchors : κ → Character) (η₀ : Character)
    (B₀ L₀ c₀ sourceMesh : ℝ) (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1) (hL : 1 < L₀) (hc0 : 0 ≤ c₀)
    (hc1 : c₀ < 1) (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (PP : PivotParams sourceMesh) (bΦ Smax Lroot : ℝ)
    (hLroot : PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) + PP.δ +
      2*PP.binWidth*Smax ≤ Lroot)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource
      ⟨B₀, L₀, 0, B₀, 0, c₀⟩ sourceMesh PP.εm) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ < PP.dmin/2 → 4*τ < PP.dmin*PP.ηw →
      2*τ < PP.dmin*PP.ηslot → ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
        (c : BufferIndex PP.e) (F : ℝ), 3/4 ≤ bufferValue PP.e c → bufferValue PP.e c ≤ 7/8 →
        PP.qlo ≤ F → F ≤ PP.Q → PP.binWidth ≤ (2*bufferValue PP.e c-1)/2 →
      ∀ (rows : Finset O) (slots : Finset Slot) (w σ v : Slot → ℝ) (t : ℝ)
        (θ : Slot → RayQuotient.Characters rayM H),
      (∀ z ∈ rows, ∃ hz : st.radial.keep z,
        OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη z hz
          PP.e (Z^τ) c ∧
        ((Ideal.span {z}).absNorm : ℝ) ≤ Z^F ∧
        ¬ (wholeRegularDictionary rayM H hH (anchors j) η₀).exceptionalCore
          (sixthFrequencyEquiv.symm ⟨z, st.row_ne_zero z hz⟩).1) →
      (∀ s ∈ slots, PP.wmin ≤ w s) → (∀ s ∈ slots, (33/50:ℝ) ≤ σ s) → (∀ s ∈ slots, σ s ≤ 33/50) →
      (∀ s ∈ slots, w s ≤ PP.mesh * PP.dmin) → ∑ s ∈ slots, w s ≤ Smax →
      |t| + Z^τ/2 ≤ (3*c.1.val+2:ℕ)*Z^τ → (∀ s ∈ slots, |t + v s| + Z^τ/2 ≤ (3*c.1.val+2:ℕ)*Z^τ) →
      ∑ z ∈ rows, (∏ s ∈ slots, max 1 ‖normalizedSlot st.character st.mask 1 z
          (primePool rayM H 2 (Z^(w s)))
          (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (v s) I) t (Z^(w s))‖)^2 ≤
        C * Z^(τ*J) *
          Z^(unmarkedDensity (2*bufferValue PP.e c-1) * F + (2*bufferValue PP.e c-1) *
            ∑ s ∈ slots, w s -
            QRH.RepeatedMarks.Source.gainC (2*bufferValue PP.e c-1) B₀ L₀ c₀
              (∑ s ∈ slots, w s) F + Lroot) := by
  obtain ⟨J, C, hC, hpiv⟩ := high_dictionary_sum_marked (Slot := Slot) rayM H hH anchors η₀ B₀ L₀ c₀
    sourceMesh hB0 hB1 hL hc0 hc1 W hWs hW hβ PP hparentSource
  have hπ : 0 < 1 + 2*Real.pi + 6*((PP.I:ℝ)+1) := by positivity
  refine ⟨J, C * (1 + 2*Real.pi + 6*((PP.I:ℝ)+1))^J, by positivity, ?_⟩
  intro τ hτ h1 h2 h3
  filter_upwards [hpiv τ hτ h1 h2 h3] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro j st hchar hpun hQM hQη c F hc34 hc78 hF hF' hbinW rows slots w σ v t θ hrows hw hσ hσ' hwm
    hS hwin hwin'
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hi : c.1.val ≤ PP.I := (Nat.lt_succ_iff.mp c.1.isLt).trans PP.hI
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hmem : ∀ u ∈ rows', u.val ∈ rows := fun u hu => Finset.mem_subtype.mp hu
  have hnz : ∀ z ∈ rows, z ≠ 0 := fun z hz => by
    obtain ⟨hk, _⟩ := hrows z hz
    exact st.row_ne_zero z hk
  let χ : NonzeroFrequency → Character := fun u =>
    excluded (naturalRow st.character u.val u.property).character st.puncture
  have hn : ∀ u ∈ rows', ∀ j', (wholeSourceFamily rayM H hH η₀ (χ u) j').residue ≠ 1 := by
    intro u hu j'
    obtain ⟨hk, _⟩ := hrows u.val (hmem u hu)
    exact whole_source_family_nonprincipal rayM H hH st η₀ hQM hQη u.val hk
      (naturalRow st.character u.val u.property) j'
  have key := hZ.2 j F (bufferValue PP.e c) c.1.val hi hc34 hc78 hF hF' hbinW rows' slots w σ v t θ χ
    (fun u hu => by
      obtain ⟨hk, hb, hnorm, hreg⟩ := hrows u.val (hmem u hu)
      exact hnorm)
    (fun u hu => by
      obtain ⟨hk, hb, hnorm, hreg⟩ := hrows u.val (hmem u hu)
      exact hreg)
    (fun u hu K => by
      change idealCoeff (excluded (naturalRow st.character u.val u.property).character
        st.puncture) K = _
      rw [hpun, hchar])
    hn
    (fun u hu hh => by
      obtain ⟨hk, hb, hnorm, hreg⟩ := hrows u.val (hmem u hu)
      exact hb.2.2.2.2.2.2.2.2)
    (fun u hu hh => by
      obtain ⟨hk, hb, hnorm, hreg⟩ := hrows u.val (hmem u hu)
      exact hb.2.2.2.2.2.1)
    hw hσ hσ' hwm hwin hwin'
  have hsum : ∑ z ∈ rows, (∏ s ∈ slots, max 1 ‖normalizedSlot st.character st.mask 1 z
        (primePool rayM H 2 (Z^(w s)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (v s) I) t (Z^(w s))‖)^2 =
      ∑ u ∈ rows', (∏ s ∈ slots, max 1 ‖WeightedHigh.labeledRawSlot rayM H hH η₀ W Z w σ v
        (fun _ : NonzeroFrequency => t) θ χ u s‖)^2 := by
    rw [← Finset.sum_subtype_of_mem
      (fun z => (∏ s ∈ slots, max 1 ‖normalizedSlot st.character st.mask 1 z
        (primePool rayM H 2 (Z^(w s)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (v s) I) t (Z^(w s))‖)^2) hnz]
    apply Finset.sum_congr rfl
    intro u hu
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    congr 2
    exact OAI.SevenEighths.Record1252270103Source.positive_raw_natural_slot
      (naturalRow st.character u.val u.property) st.puncture st.puncture_ne_zero _ _ _ _
  rw [hsum]
  refine key.trans ?_
  -- the geometry height and the loss
  set ν : ℝ := 2*bufferValue PP.e c-1 with hν
  set S : ℝ := ∑ s ∈ slots, w s with hSdef
  have hν0 : 0 ≤ ν := by rw [hν]; linarith
  have hν34 : ν ≤ 3/4 := by rw [hν]; linarith
  have hZτ : 1 ≤ Z^τ := Real.one_le_rpow hZ1.le hτ.le
  have hgeo : (1 + rawGeometryHeight Z τ PP.I)^J ≤
      (1 + 2*Real.pi + 6*((PP.I:ℝ)+1))^J * Z^(τ*J) := by
    unfold rawGeometryHeight
    have h1 : 1 + (2*Real.pi + 6*(((PP.I+1 : ℕ):ℝ)))*Z^τ ≤
        (1 + 2*Real.pi + 6*((PP.I:ℝ)+1))*Z^τ := by
      push_cast
      nlinarith [Real.pi_pos]
    calc _ ≤ ((1 + 2*Real.pi + 6*((PP.I:ℝ)+1))*Z^τ)^J := pow_le_pow_left₀ (by positivity) h1 J
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (Z^τ) J, ← Real.rpow_mul hZ0.le]
  have hρ1 : unmarkedDensity ν ≤ 1 := unmarkedDensity_le_one' hν0 hν34
  have hexp : PP.dmax*(155*PP.εp + PP.mesh + PP.εm + ν*PP.ζ + PP.η) + unmarkedDensity ν * PP.δ +
      2*PP.binWidth*S ≤ Lroot := by
    have hdm : 0 ≤ PP.dmax := PP.hdmin.le.trans PP.hdmax
    have h1 : ν*PP.ζ ≤ (3/4)*PP.ζ := mul_le_mul_of_nonneg_right hν34 PP.hζ.le
    have h2 : PP.dmax*(155*PP.εp + PP.mesh + PP.εm + ν*PP.ζ + PP.η) ≤
        PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) :=
      mul_le_mul_of_nonneg_left (by linarith) hdm
    have h3 : unmarkedDensity ν * PP.δ ≤ PP.δ := by nlinarith [PP.hδ]
    have h4 : 2*PP.binWidth*S ≤ 2*PP.binWidth*Smax :=
      mul_le_mul_of_nonneg_left hS (by linarith [PP.hbin])
    linarith
  have hZe : Z^(unmarkedDensity ν * F + ν * S -
        QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ S F +
        PP.dmax*(155*PP.εp + PP.mesh + PP.εm + ν*PP.ζ + PP.η) +
        unmarkedDensity ν * PP.δ + 2*PP.binWidth*S) ≤
      Z^(unmarkedDensity ν * F + ν * S - QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ S F + Lroot) :=
    Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  calc C * (1 + rawGeometryHeight Z τ PP.I)^J * Z^(unmarkedDensity ν * F + ν * S -
        QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ S F +
        PP.dmax*(155*PP.εp + PP.mesh + PP.εm + ν*PP.ζ + PP.η) +
        unmarkedDensity ν * PP.δ + 2*PP.binWidth*S)
      ≤ C * ((1 + 2*Real.pi + 6*((PP.I:ℝ)+1))^J * Z^(τ*J)) *
        Z^(unmarkedDensity ν * F + ν * S - QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ S F + Lroot) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hgeo hC.le) hZe (Real.rpow_nonneg hZ0.le _)
          (by positivity)
    _ = _ := by ring

/-- **Exceptional rows.** The raw rows of the whole-source dictionary whose free core is
exceptional have cores in a finite set (independent of `Z`); by Collet's `finite_core_raw_count`
there are at most `Cex·H^{1/6}` of them with `N(z) ≤ H`. -/
theorem high_exceptional_count {κ : Type} [Fintype κ] (anchors : κ → Character)
    (η₀ : Character) :
    ∃ Cex : ℝ, 0 < Cex ∧ ∀ (j : κ) (Hn : ℝ), 1 ≤ Hn → ∀ rows : Finset O,
      (∀ z ∈ rows, ∃ hz0 : z ≠ 0, ((Ideal.span {z}).absNorm : ℝ) ≤ Hn ∧
        (wholeRegularDictionary rayM H hH (anchors j) η₀).exceptionalCore
          (sixthFrequencyEquiv.symm ⟨z, hz0⟩).1) →
      (rows.card : ℝ) ≤ Cex * Hn^(1/6:ℝ) := by
  have hfin : ∀ j : κ, {u : FreeRow | (wholeRegularDictionary rayM H hH (anchors j) η₀).exceptionalCore
      u}.Finite := fun j =>
    FixedUnmarkedDictionary.exceptional_cores_finite (wholeRegularDictionary rayM H hH (anchors j) η₀)
  let E : κ → Finset FreeRow := fun j => (hfin j).toFinset
  refine ⟨(∑ j, (E j).card : ℝ) * 128 + 1, by positivity, ?_⟩
  intro j Hn hHn rows hrows
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hz0, _⟩ := hrows z hz
    exact hz0
  have hcnt := finite_core_raw_count (E j) Hn hHn rows' (by
    intro u hu
    obtain ⟨hz0, hnorm, hexc⟩ := hrows u.val (Finset.mem_subtype.mp hu)
    refine ⟨hnorm, ?_⟩
    simp only [E, Set.Finite.mem_toFinset]
    exact hexc)
  rw [hcard] at hcnt
  have hEj : ((E j).card : ℝ) ≤ ∑ j', ((E j').card : ℝ) :=
    Finset.single_le_sum (f := fun j' => ((E j').card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_univ j)
  have hH0 : 0 ≤ Hn^(1/6:ℝ) := Real.rpow_nonneg (zero_le_one.trans hHn) _
  refine hcnt.trans ?_
  have : ((E j).card : ℝ) * 128 ≤ (∑ j', ((E j').card : ℝ)) * 128 + 1 := by linarith
  exact mul_le_mul_of_nonneg_right this hH0

end
end
end QRH.ArviDensity.Density
