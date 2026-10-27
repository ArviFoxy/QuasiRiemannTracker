/- Copyright (c) 2026 Sil. Apache-2.0.
LOW branch of the density-split leaf (DS §4, final source audit §§2, 4).

On the LOW rows of the q-free buffered selector (`lowRow`: some actual bin lies strictly
below `(q+1)/2`), PR69 `retained_zero_bin_low` gives the genuine upper guard
`ActualLow … ((q+1)/2) e (3(p+1)T₀)` on the whole ray-twisted family. The uniform-in-`q`
slot supplier (`Density/UniformLow.uniform_low_slots_parent_mask`, built on PR69
`actual_high_slots`: one constant and one threshold, then `∀ q`) bounds every erased slot
by `C·Z^{2εd}·Z^{q·w}`. Partial deletion (`CubeFree/Leaf/PartialDeletion`) then erases the
slots `T \ F` on the LOW rows, and the retained LOW energy is at most the whole retained
energy (positivity). The base height is `T₀ = (h+1)Z^τ`; the supplier height index of
buffer height `p` is `binIndex p h`. -/
import Submissions.sil_density_split_20261026.Density.LeafRows
import Submissions.sil_density_split_20261026.Density.UniformLow

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.SilDensitySplit.Density
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion
open LocalMoment
local notation "O" => HeckeFamily.O

/-- The squared norm of a product of slots bounded slot by slot. -/
theorem prod_slots_le {α : Type*} (D : Finset α) (s : α → ℂ) (c Z q : ℝ) (w : α → ℝ)
    (hZ : 0 < Z) (hc : 0 ≤ c) (h : ∀ i ∈ D, ‖s i‖^2 ≤ c*Z^(q*w i)) :
    ‖∏ i ∈ D, s i‖^2 ≤ c^D.card * Z^(q*∑ i ∈ D, w i) := by
  rw [norm_prod, ← Finset.prod_pow]
  calc ∏ i ∈ D, ‖s i‖^2 ≤ ∏ i ∈ D, (c*Z^(q*w i)) :=
        Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) h
    _ = c^D.card * Z^(q*∑ i ∈ D, w i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum,
          Real.rpow_sum_of_pos hZ]

section
variable (rayM : Ideal O) [NeZero rayM]
local instance leafLowQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **LOW branch.** One constant, then the anchor `η₀`, then one threshold in `Z`; only
then the cut `q`, the state, the base height, the slot data and the retained set `F`.
On the LOW rows the erased slots `T \ F` cost `(C·Z^{2εd})^{|T\F|}·Z^{q·∑_{T\F} w}`, and
the retained LOW energy is bounded by the whole retained energy. -/
theorem low_branch {α : Type*} [DecidableEq α]
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ)
    (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ q : ℝ, 1/50 ≤ q → q ≤ 1 →
      ∀ st : NaturalState Z 0 bΦ, st.puncture = 1 → st.width ≤ Mcap →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus) (h : ℕ),
      ∀ (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ) (t : ℝ)
        (T F : Finset α), F ⊆ T →
      (∀ i ∈ T, 0 ≤ w i) → (∀ i ∈ T, w i/d ≤ Rwidth) →
      (∀ i ∈ T, σmin ≤ σ i) → (∀ i ∈ T, σ i ≤ σmax) →
      (∀ i ∈ T, |t + v i| + Z^τ/2 ≤ (3*h+2 : ℕ)*Z^τ) →
      (3 + 3*(((bufferCount e + 1)*(h+1) : ℕ) : ℝ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ), 0 ≤ X₁*X₂ →
      energy st.character st.mask 1 t W₁ W₂
        (fun i:T => primePool rayM H 2 (Z^(w i)))
        (fun (i:T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i:T => Z^(w i)) X₁ X₂
        (fun z => st.radial.keep z ∧
          lowRow rayM H hH st η₀ hQM hQη e (((h+1 : ℕ) : ℝ)*Z^τ) q z)
        st.radial.profile st.radial.scale ≤
      ((C*Z^(2*ε*d))^((T \ F).card) * Z^(q*∑ i ∈ T \ F, w i)) *
        energy st.character st.mask 1 t W₁ W₂
        (fun i:F => primePool rayM H 2 (Z^(w i)))
        (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i:F => Z^(w i)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale := by
  obtain ⟨C, hC, hslots⟩ := uniform_low_slots_parent_mask rayM H hH W 1 2 one_pos hWs hW
    Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap 0 1 d hRw hdmax hτ hε he he' hκ hη hbudget
    hbΦ one_pos hd hdsupply hdm
  refine ⟨C, hC, fun η₀ => ?_⟩
  filter_upwards [hslots η₀] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro q hq0 hq1 st hu hwidth hQM hQη h θ w σ v t T F hFT hw hwr hσ hσ' hwin hgate
    W₁ W₂ X₁ X₂ hX
  have hZ0 : 0 < Z := zero_lt_one.trans hZ.1
  have hZτ : 0 ≤ Z^τ := Real.rpow_nonneg hZ0.le _
  set T₀ : ℝ := ((h+1 : ℕ) : ℝ)*Z^τ with hT₀
  let L : O → Prop := lowRow rayM H hH st η₀ hQM hQη e T₀ q
  let stL := restrictState st L
  let c : ℝ := C*Z^(2*ε*d)
  have hc : 0 ≤ c := by positivity
  have hdel := CubeFree.energy_partial_delete stL hu T F hFT
    (fun i => primePool rayM H 2 (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i => Z^(w i)) (fun _ => Real.rpow_nonneg hZ0.le _) W₁ W₂ t X₁ X₂
    (c^((T \ F).card) * Z^(q*∑ i ∈ T \ F, w i)) hX ?_
  · refine hdel.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact energy_mono_keep st.character st.mask 1 t W₁ W₂ _ _ _ X₁ X₂ st.radial.keep
      stL.radial.keep (fun z hz => hz.1) st.radial.profile st.radial.scale bΦ
      (fun z => st.radial.nonneg z) st.radial.scale_pos st.radial_support
  · intro z hk hp
    obtain ⟨hk0, hz, p, hbin, hlow⟩ := hk
    have hAL := OAI.SevenEighths.Record1252270103Source.retained_zero_bin_low rayM H hH
      st η₀ hQM hQη z hz e T₀ q p hbin hlow hp
    rw [hT₀, binIndex_height] at hAL
    have hpB : p.1.val ≤ bufferCount e := hbin.2.1
    apply prod_slots_le (T \ F) _ c Z q w hZ0 hc
    intro i hi
    have hiT : i ∈ T := (Finset.mem_sdiff.mp hi).1
    have hh := hZ.2 q hq1 st hwidth hQM hQη ((q+1)/2) (binIndex p.1.val h)
      (by linarith) (by linarith) (w i) (σ i) t (v i) (hw i hiT) (hwr i hiT)
      (hσ i hiT) (hσ' i hiT) (window_binIndex p.1.val h hZτ (hwin i hiT))
      (gate_binIndex p.1.val h (bufferCount e) 2 hZτ hpB hgate) z hz hAL (θ i) 1 1
      (by rw [hu, mul_one]) (fun I _ => isCoprime_one_right)
    rw [slot_unit_mask (naturalRow st.character z (st.row_ne_zero z hz))] at hh
    exact hh

end
end
end QRH.SilDensitySplit.Density
