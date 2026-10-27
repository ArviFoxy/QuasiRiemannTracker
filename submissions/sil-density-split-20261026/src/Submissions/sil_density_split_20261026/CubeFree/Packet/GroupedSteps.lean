/- Copyright (c) 2026 Sil. Apache-2.0.
The three analytic inputs of the grouped side bound on the concrete frame (Seam B, WP-H).

* `label_reduction_frame`: WP-G's `label_reduction_single` on a fitting label: its literal
  energy is `≤ 0`, or at most the label mass times ONE canonical packed child, written on
  the sublattice `V₀A₂·O` of the anchor's source keep at scale `N(V₀A₂)·K` (`childE`). The
  child depends on the label only through the anchor index, the slot set and the two
  (shortened) ordinary lengths; the label mass is `≤ C Z^ε X` (`labelMass_le`).
* `class_source`: Seam A (`PricedPackedAt`) at the ONE common scale `Kc`, row multiplier
  `V = 1`, for the label-independent common profiles `commonPair e τ` at `c_e Yᵢ`; the price
  is evaluated at the source's widths by `Price.mono`.
* `profile_mass`: the spectral masses of the two source profiles (heights `2π tᵢ + v`) are
  polynomial in the source height and in `v`. -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedFrame
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceUniformApproximation
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.SilDensitySplit.CubeFree.Packet.Grouped
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP QRH.SilDensitySplit.CubeFree.Packet.Reduce

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open NativeFiniteHoles NativeInjectiveEnergy
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedCommonSource MixedOriginalSource MixedRestrictedDictionary MixedHeightEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyChildState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergySlotHeight
open CenteredMomentEnergyAllocatedChildren CenteredMomentLattice CenteredMomentTwist
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots CenteredMomentHeckeExpansion
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
open ProfileSeparation (commonPair scale pairWeight pairMajorant)
local notation "O" => HeckeFamily.O

local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- The two ordinary profiles of the source at height `v`. -/
def GSrc.prof (r : GSrc θ mesh Z) (v : ℝ) : Profiles θ.a θ.b :=
  independentProfiles θ.ha0 r.W₁ r.W₂ r.hs₁ r.hs₂ (2*Real.pi*(r.t₁+v/(2*Real.pi)))
    (2*Real.pi*(r.t₂+v/(2*Real.pi)))

/-- The slot pools, coefficients and scales of a slot set. -/
def GSrc.pools (r : GSrc θ mesh Z) (A : Finset (Fin θ.N)) : A → Finset (Ideal O) :=
  fun i => primePool θ.rayM θ.Hray 2 (Z^(r.w i))
def GSrc.coeffs (r : GSrc θ mesh Z) (v : ℝ) (A : Finset (Fin θ.N)) : A → Ideal O → ℂ :=
  fun i I => idealCoeff (relativeCharacter θ.rayM θ.Hray θ.hH θ.η₀ (r.χ i)) I *
    HeckePrimeAnnular.annularWeight θ.W (Z^(r.w i)) (r.σ i) (r.t+v+r.freq i) I
def GSrc.scales (r : GSrc θ mesh Z) (A : Finset (Fin θ.N)) : A → ℝ := fun i => Z^(r.w i)

/-- The packed mask `fixedBadMask · idealGenerator 1`. -/
abbrev pmask : O := fixedBadMask * ConcretePrimeRowBridge.idealGenerator 1

/-- The canonical packed child of a label: anchor `j`, slot set `A`, ordinary lengths
`X₁, X₂`, on the sublattice `V·O` at scale `N(V)·K`. -/
def childE (η : Character) (r : GSrc θ mesh Z) (v : ℝ) (j : DictIdx) (A : Finset (Fin θ.N))
    (X₁ X₂ : ℝ) (V : O) (K : ℝ) : ℝ :=
  energy (anchors η j) pmask 1 0 ((r.prof v).profile 0) ((r.prof v).profile 1)
    (r.pools A) (r.coeffs v A) (r.scales A) X₁ X₂
    (fun y => V ∣ y ∧ initialKeep (anchors η j) (internalQ θ.Q θ.η₀) y) ballProfile
    (((Ideal.span {V}).absNorm : ℝ) * K)

/-! ### Label reduction on the frame -/

theorem label_reduction_frame (θ : GData L) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cred : ℝ, 0 < Cred ∧ ∀ (mesh Z : ℝ), mesh ≤ 1 → ∀ (η : Character)
      (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η r x) (v : ℝ),
      rawEnergy η r x h v ≤ 0 ∨
      ∃ (A : Finset (Fin θ.N)) (X₁' X₂' : ℝ), 0 < X₁' ∧ 0 < X₂' ∧
        ((X₁' ≤ r.X₁ ∧ X₂' ≤ r.X₂) ∨ (X₁' ≤ r.Y₁ ∧ X₂' ≤ r.Y₂)) ∧
        rawEnergy η r x h v ≤ labelMass Cred Z ε δ r.w r.X₁ r.X₂ x.G x.D x.d *
          childE η r v (x.anchor r) A X₁' X₂' (r.V₀ * x.twist) (dyadicScale (x.n 1)) := by
  obtain ⟨C, hC, hred⟩ := label_reduction_single θ.rayM θ.Hray θ.hH (α := Fin θ.N) θ.Holes θ.W
    θ.a θ.b L 1 θ.Lcap θ.Cap θ.Bmask ε δ (33/50) (33/50) θ.hWs θ.hW θ.ha0 θ.hb1
    zero_le_one θ.hLcap θ.hCap θ.hBmask θ.hCapb θ.hLL hε hδ
  refine ⟨C, hC, ?_⟩
  intro mesh Z hmesh η r x hx v
  rcases hred Z r.hZ.le θ.η₀ r.χ r.w r.σ r.freq r.t r.R₀ r.hw (fun i => (r.hwm i).trans hmesh)
      (fun i => (r.hσ i).ge) (fun i => (r.hσ i).le) r.hR₀ (x.char r) (anchors η (x.anchor r))
      (internalQ θ.Q θ.η₀) x.n (r.V₀ * x.twist) (x.mask r) (mul_ne_zero r.hV₀ hx.twist_ne)
      hx.mask_ne hx.coef x.R x.G x.seed x.D hx.R_ne hx.G_ne hx.seed_dvd hx.D_sq hx.G_mask
      x.holesH hx.holes_sub hx.cap hx.holes_R₀ r.W₁ r.W₂ r.hs₁ r.hs₂ r.t₁ r.t₂ r.X₁ r.X₂
      r.Y₁ r.Y₂ r.hX₁ r.hX₂ r.hY₁ r.hY₂ r.hX₁L r.hX₂L r.hY₁L r.hY₂L r.hXY x.d
      ⟨hx.d₁, hx.d₂⟩ v with h0 | ⟨A, X₁', X₂', h1, h2, h3, h4⟩
  · exact Or.inl h0
  · refine Or.inr ⟨A, X₁', X₂', h1, h2, h3, ?_⟩
    unfold childE GSrc.prof GSrc.pools GSrc.coeffs GSrc.scales
    rw [energy_sublattice_eq (anchors η (x.anchor r)) _ _ (mul_ne_zero r.hV₀ hx.twist_ne)]
    exact h4

theorem one_le_absNorm (I : Ideal O) (hI : I ≠ 0) : (1:ℝ) ≤ (I.absNorm : ℝ) := by
  have h : I.absNorm ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

theorem rpow_half_le (N : ℝ) (hN : 1 ≤ N) : N^(1/2:ℝ) ≤ N := by
  calc N^(1/2:ℝ) ≤ N^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = N := Real.rpow_one N

/-- The label mass is at most `C Z^ε X`. -/
theorem labelMass_le {α : Type*} [Fintype α] (C Z ε : ℝ) (hC : 0 ≤ C) (hZ : 0 < Z)
    (w : α → ℝ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (G D : Ideal O) (hG : G ≠ 0)
    (hD : D ≠ 0) (d : Ideal O × Ideal O) (hd₁ : d.1 ≠ 0) (hd₂ : d.2 ≠ 0) :
    labelMass C Z ε (1/2) w X₁ X₂ G D d ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) := by
  have hG1 := one_le_absNorm G hG
  have hD1 := one_le_absNorm D hD
  have hp : (1:ℝ) ≤ pairNorm d := by
    unfold pairNorm
    have := one_le_absNorm _ hd₁
    have := one_le_absNorm _ hd₂
    nlinarith
  have hX : 0 ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) := by
    have : 0 < ∏ i, Z^(w i) := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos hZ _
    have := Real.rpow_pos_of_pos hZ ε
    positivity
  unfold labelMass
  rw [div_div, div_div, div_le_iff₀ (mul_pos (by linarith) (mul_pos (by linarith) (by linarith)))]
  have hGh := rpow_half_le _ hG1
  have hDh := rpow_half_le _ hD1
  have hGh0 : 0 ≤ (G.absNorm : ℝ)^(1/2:ℝ) := Real.rpow_nonneg (by linarith) _
  have hDh0 : 0 ≤ (D.absNorm : ℝ)^(1/2:ℝ) := Real.rpow_nonneg (by linarith) _
  calc C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) * (G.absNorm : ℝ)^(1/2:ℝ) * (D.absNorm : ℝ)^(1/2:ℝ)
      ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) * (G.absNorm : ℝ) * (D.absNorm : ℝ) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hGh hX) hDh hDh0
        exact mul_nonneg hX (by linarith)
    _ ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) *
          ((G.absNorm : ℝ) * (pairNorm d * (D.absNorm : ℝ))) := by
        have h1 : 0 ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) * (G.absNorm : ℝ) * (D.absNorm : ℝ) :=
          by positivity
        nlinarith

/-- The extracted pair gain: `pairNorm d · labelMass … d` is the label mass at the unit pair. -/
theorem labelMass_pair {α : Type*} [Fintype α] (C Z ε δ : ℝ) (w : α → ℝ) (X₁ X₂ : ℝ)
    (G D : Ideal O) (d : Ideal O × Ideal O) (hd₁ : d.1 ≠ 0) (hd₂ : d.2 ≠ 0) :
    pairNorm d * labelMass C Z ε δ w X₁ X₂ G D d = labelMass C Z ε δ w X₁ X₂ G D (⊤, ⊤) := by
  have hp : pairNorm d ≠ 0 := (pairNorm_pos hd₁ hd₂).ne'
  have h1 : pairNorm ((⊤, ⊤) : Ideal O × Ideal O) = 1 := by
    simp [pairNorm, Ideal.absNorm_top]
  unfold labelMass
  rw [h1, div_one]
  field_simp

/-! ### Seam A at the common scale -/

theorem ball_support_bΦ (bΦ : ℝ) (hb : 2 ≤ bΦ) :
    Function.support (ballProfile : ℝ → ℂ) ⊆ Set.Iic bΦ :=
  fun x hx => (Set.mem_Iic.mp (ball_support hx)).trans hb

theorem pairWeight_two_mul (n : ℕ) (τ : ℝ × ℝ) :
    pairWeight (2*n) τ = (pairWeight n τ)^2 := by
  unfold pairWeight
  rw [show 2*n = n*2 by ring, pow_mul, pow_mul]
  ring

theorem class_source (price : Price) (Mmin Mmax : ℝ) (η : Character) (r : GSrc θ mesh Z)
    (v w₀ εA : ℝ) (degA : ℕ) (SA : Finset (ℕ×ℕ)) (CA : ℝ) (hCA : 0 ≤ CA) (j : DictIdx)
    (hPA : PricedPackedAt (α := Fin θ.N) θ.rayM θ.Hray θ.hH price w₀ θ.W θ.bΦ mesh Mmin
      (Mmax+1) (L+1) εA Z (anchors η j) θ.η₀ θ.Q degA SA CA)
    (nP : ℕ) (CP : ℝ) (hctl : ∀ e τ, (commonPair e τ).control SA ≤ CP * pairWeight nP τ)
    (A : Finset (Fin θ.N)) (Y₁ Y₂ Kc Pbd : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hKc : 0 < Kc)
    (hM₁ : Mmin ≤ Real.logb Z Kc) (hM₂ : Real.logb Z Kc ≤ Mmax + 1)
    (hlen : ∀ e : Fin 2, length Z (scale e * Y₁) ≤ L + 1 ∧ length Z (scale e * Y₂) ≤ L + 1)
    (hP : ∀ e : Fin 2 × Fin 2, length Z (scale e.1 * Y₁) + length Z (scale e.2 * Y₂) ≤ Pbd) :
    ∀ (e : Fin 2 × Fin 2) (τ : ℝ × ℝ),
      energy (anchors η j) pmask 1 0 ((commonPair e τ).profile 0) ((commonPair e τ).profile 1)
        (r.pools A) (r.coeffs v A) (r.scales A) (scale e.1 * Y₁) (scale e.2 * Y₂)
        (initialKeep (anchors η j) (internalQ θ.Q θ.η₀)) ballProfile Kc ≤
      (CA * CP^2) * pairWeight (2*nP) τ *
        (QuadraticInitialBound.diagonalControl ballProfile *
          (1 + |(0:ℝ)| + (|r.t| + |v| + r.Vf))^degA *
          Z^(Real.logb Z Kc + price.f w₀ Pbd (∑ i, r.w i) (Real.logb Z Kc) + εA)) := by
  intro e τ
  have hZ1 : 1 ≤ Z := r.hZ.le
  have hv : ∀ i : A, |r.t + v + r.freq i| ≤ |r.t| + |v| + r.Vf := by
    intro i
    calc |r.t + v + r.freq i| ≤ |r.t + v| + |r.freq i| := abs_add_le _ _
      _ ≤ |r.t| + |v| + r.Vf := by linarith [abs_add_le r.t v, r.hfreq i]
  have hN1 : (((Ideal.span {(1:O)}).absNorm : ℕ) : ℝ) = 1 := by
    rw [Ideal.span_singleton_one, Ideal.absNorm_top, Nat.cast_one]
  have h := hPA A (fun i => r.χ i) (fun i => r.w i) (fun i => r.σ i)
    (fun i => r.t + v + r.freq i) 0 (|r.t| + |v| + r.Vf) (fun i => r.hw i) (fun i => r.hwm i)
    (fun i => (r.hσ i).ge) (fun i => (r.hσ i).le) (by linarith [abs_nonneg r.t, abs_nonneg v, r.hVf])
    hv 1 Kc one_ne_zero hKc (by rw [hN1, one_mul]; exact hM₁) (by rw [hN1, one_mul]; exact hM₂)
    ballProfile (ball_support_bΦ θ.bΦ θ.hbΦ) (fun x => ballProfile_nonneg x) (commonPair e τ)
    (scale e.1 * Y₁) (scale e.2 * Y₂) (mul_pos (ProfileSeparation.scale_pos _) hY₁)
    (mul_pos (ProfileSeparation.scale_pos _) hY₂) (hlen e.1).1 (hlen e.2).2
  have hk : (fun z : O => initialKeep (anchors η j) (internalQ θ.Q θ.η₀) (1*z)) =
      initialKeep (anchors η j) (internalQ θ.Q θ.η₀) := funext fun z => by rw [one_mul]
  rw [hk, hN1, one_mul] at h
  refine h.trans ?_
  have hs : ∑ i : A, r.w i ≤ ∑ i, r.w i := by
    rw [Finset.sum_coe_sort A (fun i => r.w i)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => r.hw i)
  have hprice := price.mono w₀ Pbd (length Z (scale e.1 * Y₁) + length Z (scale e.2 * Y₂))
    (∑ i, r.w i) (∑ i : A, r.w i) (Real.logb Z Kc) (hP e) hs
  have hctl2 : ((commonPair e τ).control SA)^2 ≤ CP^2 * pairWeight (2*nP) τ := by
    rw [pairWeight_two_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Profiles.control_nonneg _ _) (hctl e τ) 2
  have hd := QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hH0 : 0 ≤ (1 + |(0:ℝ)| + (|r.t| + |v| + r.Vf))^degA := by
    apply pow_nonneg; linarith [abs_nonneg r.t, abs_nonneg v, r.hVf, abs_nonneg (0:ℝ)]
  have hZe : Z^(Real.logb Z Kc + price.f w₀ (length Z (scale e.1 * Y₁) +
        length Z (scale e.2 * Y₂)) (∑ i : A, r.w i) (Real.logb Z Kc) + εA) ≤
      Z^(Real.logb Z Kc + price.f w₀ Pbd (∑ i, r.w i) (Real.logb Z Kc) + εA) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hZ0 : 0 ≤ Z^(Real.logb Z Kc + price.f w₀ (length Z (scale e.1 * Y₁) +
        length Z (scale e.2 * Y₂)) (∑ i : A, r.w i) (Real.logb Z Kc) + εA) :=
    Real.rpow_nonneg (by linarith) _
  calc CA * QuadraticInitialBound.diagonalControl ballProfile * ((commonPair e τ).control SA)^2 *
        (1 + |(0:ℝ)| + (|r.t| + |v| + r.Vf))^degA *
        Z^(Real.logb Z Kc + price.f w₀ (length Z (scale e.1 * Y₁) +
          length Z (scale e.2 * Y₂)) (∑ i : A, r.w i) (Real.logb Z Kc) + εA)
      ≤ CA * QuadraticInitialBound.diagonalControl ballProfile * (CP^2 * pairWeight (2*nP) τ) *
        (1 + |(0:ℝ)| + (|r.t| + |v| + r.Vf))^degA *
        Z^(Real.logb Z Kc + price.f w₀ Pbd (∑ i, r.w i) (Real.logb Z Kc) + εA) := by
        apply mul_le_mul _ hZe hZ0 (mul_nonneg (mul_nonneg (mul_nonneg hCA hd)
          (mul_nonneg (sq_nonneg _) (ProfileSeparation.pairWeight_nonneg _ _))) hH0)
        apply mul_le_mul_of_nonneg_right _ hH0
        exact mul_le_mul_of_nonneg_left hctl2 (mul_nonneg hCA hd)
    _ = _ := by ring

/-! ### Spectral masses of the source profiles -/

theorem prof_profile_zero (r : GSrc θ mesh Z) (v : ℝ) :
    (r.prof v).profile 0 = CompletedHeight.uniformTwistedSchwartz r.W₁ θ.a θ.b θ.ha0 r.hs₁
      (r.W₁.smooth ⊤) (r.t₁ + v/(2*Real.pi)) := by
  simp only [GSrc.prof, independentProfiles, ite_true, normPowerProfile]
  congr 1
  field_simp

theorem prof_profile_one (r : GSrc θ mesh Z) (v : ℝ) :
    (r.prof v).profile 1 = CompletedHeight.uniformTwistedSchwartz r.W₂ θ.a θ.b θ.ha0 r.hs₂
      (r.W₂.smooth ⊤) (r.t₂ + v/(2*Real.pi)) := by
  simp only [GSrc.prof, independentProfiles, show (1:Fin 2) ≠ 0 by decide, ite_false,
    normPowerProfile]
  congr 1
  field_simp

theorem prof_support (r : GSrc θ mesh Z) (v : ℝ) (i : Fin 2) :
    Function.support (((r.prof v).profile i : 𝓢(ℝ,ℂ)) : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4) :=
  ((r.prof v).support i).trans (Set.Icc_subset_Icc θ.ha θ.hb)

theorem phase_le (s v H : ℝ) (hH : 1 + |s| ≤ H) :
    1 + ‖s + v/(2*Real.pi)‖ ≤ H * (1 + ‖v‖) := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have h1 : |v/(2*Real.pi)| ≤ |v| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    exact div_le_self (abs_nonneg v) hpi
  have h2 : |s + v/(2*Real.pi)| ≤ |s| + |v| := (abs_add_le _ _).trans (by linarith)
  have hv := abs_nonneg v
  have hs := abs_nonneg s
  nlinarith

/-- One weighted spectral mass of the source pair, against the source height. -/
theorem profile_mass (r : GSrc θ mesh Z) (v : ℝ) (J : ℕ) (T : Finset (ℕ×ℕ)) (KM : ℝ)
    (hm : ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)) (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
      (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (e : Fin 2 × Fin 2),
      ∫ τ : ℝ × ℝ, pairMajorant W₁ W₂ hs₁ hs₂ e τ * pairWeight J τ ≤
        KM * (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))
    (n : ℕ) (S : Finset (ℕ×ℕ)) (Ct : ℝ) (hCt : 0 ≤ Ct)
    (htw : ∀ (W : 𝓢(ℝ,ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc θ.a θ.b) (t : ℝ),
      T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (CompletedHeight.uniformTwistedSchwartz W θ.a θ.b θ.ha0 hs (W.smooth ⊤) t) ≤
        Ct * sourceControl S W * (1+‖t‖)^n) (hKM : 0 ≤ KM) :
    ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ, 1 * pairMajorant ((r.prof v).profile 0)
        ((r.prof v).profile 1) (prof_support r v 0) (prof_support r v 1) e τ * pairWeight J τ ≤
      4 * (KM * (Ct^2 * (sourceControl S r.W₁ * sourceControl S r.W₂) *
        (r.height * (1 + ‖v‖))^(2*n))) := by
  have hH₁ : 1 + |r.t₁| ≤ r.height := by
    unfold GSrc.height; linarith [abs_nonneg r.t, r.hVf, abs_nonneg r.t₂]
  have hH₂ : 1 + |r.t₂| ≤ r.height := by
    unfold GSrc.height; linarith [abs_nonneg r.t, r.hVf, abs_nonneg r.t₁]
  have hb₁ : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((r.prof v).profile 0) ≤
      Ct * sourceControl S r.W₁ * (r.height * (1 + ‖v‖))^n := by
    rw [prof_profile_zero]
    refine (htw r.W₁ r.hs₁ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCt (sourceControl_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (phase_le _ _ _ hH₁) n
  have hb₂ : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((r.prof v).profile 1) ≤
      Ct * sourceControl S r.W₂ * (r.height * (1 + ‖v‖))^n := by
    rw [prof_profile_one]
    refine (htw r.W₂ r.hs₂ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCt (sourceControl_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (phase_le _ _ _ hH₂) n
  have hcell : ∀ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ, 1 * pairMajorant ((r.prof v).profile 0)
      ((r.prof v).profile 1) (prof_support r v 0) (prof_support r v 1) e τ * pairWeight J τ ≤
      KM * (Ct^2 * (sourceControl S r.W₁ * sourceControl S r.W₂) *
        (r.height * (1 + ‖v‖))^(2*n)) := by
    intro e
    simp_rw [one_mul]
    refine (hm _ _ _ _ e).trans ?_
    apply mul_le_mul_of_nonneg_left _ hKM
    have h0 := apply_nonneg (T.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ((r.prof v).profile 0)
    have h1 := apply_nonneg (T.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ((r.prof v).profile 1)
    calc T.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((r.prof v).profile 0) *
          T.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((r.prof v).profile 1)
        ≤ (Ct * sourceControl S r.W₁ * (r.height * (1 + ‖v‖))^n) *
          (Ct * sourceControl S r.W₂ * (r.height * (1 + ‖v‖))^n) :=
          mul_le_mul hb₁ hb₂ h1 (h0.trans hb₁)
      _ = _ := by ring
  calc _ ≤ ∑ _e : Fin 2 × Fin 2, KM * (Ct^2 * (sourceControl S r.W₁ * sourceControl S r.W₂) *
        (r.height * (1 + ‖v‖))^(2*n)) := Finset.sum_le_sum fun e _ => hcell e
    _ = _ := by rw [Finset.sum_const, Finset.card_univ]; simp

end
end QRH.SilDensitySplit.CubeFree.Packet.Grouped
