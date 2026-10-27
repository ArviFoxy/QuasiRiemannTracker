/- Copyright (c) 2026 Sil. Apache-2.0.
HIGH energy of the density-split leaf: count times pointwise, summed over the finitely
many buffered bins (DS §3, final source audit §5).

The HIGH rows (kept, not LOW at the cut `q`) are classified by their q-free chosen bin
(`selectBin`). A class `c` is nonempty only if `(q+1)/2 ≤ b_c ≤ 7/8`; then
`ν = 2b_c - 1 ∈ [q, 3/4]`, each row has `|row|² ≤ K·ctl²·Z^{ν(P+s)+small}`
(`high_row_bound`) and the class has at most `C(1+3p T₀)^J (bΦ Z^M)^{ρ(ν)+loss}` rows
(`high_row_count`). By `energy_le_classes` and `high_exponent` the HIGH energy is at most
`K'·diag·ctl²·(1+|t|+height)^J·Z^{M + highSup q P s M + small + loss·Mcap + τJ}`. -/
import Submissions.sil_density_split_20261026.Density.LeafHigh

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QRH.SilDensitySplit.Density
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
local notation "O" => HeckeFamily.O

section
variable (rayM : Ideal O) [NeZero rayM]
local instance leafHighEnergyQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **HIGH branch.** The dictionary (anchors, `η₀`) and the loss are fixed first; the
density degree `J` comes next; then for every height scale `τ > 0` one constant, one
control set and one threshold, uniformly in the anchor index, the cut `q ∈ [13/20,3/4]`,
the state, the base height index `h`, the slot data, the ordinary profiles and lengths. -/
theorem high_branch {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ : ℝ) (hbΦ : 1 ≤ bΦ) {κ : Type} [Fintype κ] (anchors : κ → Character)
    (η₀ : Character)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hβ' : HeckeZeroSupremum.beta ≤ 7/8)
    (Mcap Lplain ε₁ e kap v d loss : ℝ) (hL : 0 ≤ Lplain)
    (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000) (hkap : 0 < kap) (hkap' : kap ≤ 1)
    (hv : 0 ≤ v) (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d)
    (hslotBudget : 8*e*(1/d)+kap ≤ ε₁)
    (hplainBudget : 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) :
    ∃ J : ℕ, ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 < K ∧ ∃ S : Finset (ℕ×ℕ),
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 2 < Z^τ ∧
      ∀ (j : κ) (q : ℝ), 13/20 ≤ q → q ≤ 3/4 →
      ∀ st : NaturalState Z 0 bΦ, st.character = anchors j → st.puncture = 1 →
        st.width ≤ Mcap →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus) (h : ℕ),
      ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ)
        (t height : ℝ),
      (∀ k, 0 ≤ w k) → (∀ k, w k ≤ 1) →
      (∀ k, (33/50:ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
      0 ≤ height → (∀ k, |v' k| ≤ height) →
      |t| + height + Z^τ/2 ≤ (3*h+2 : ℕ)*Z^τ → (h:ℝ) ≤ |t| + height + 1 →
      (3 + 3*(((bufferCount e + 1)*(h+1) : ℕ) : ℝ)*Z^τ)^4 ≤ (Z^d)^v →
      ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
        (fun k => Z^(w k)) X₁ X₂
        (fun z => st.radial.keep z ∧
          ¬ lowRow rayM H hH st η₀ hQM hQη e (((h+1 : ℕ) : ℝ)*Z^τ) q z)
        st.radial.profile st.radial.scale ≤
      K * QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
        (1+|t|+height)^J *
        Z^(st.rowWidth + highSup q (length Z X₁ + length Z X₂) (∑ k, w k) st.rowWidth +
          (2*ε₁*d*(Fintype.card α + 1) + loss*Mcap + τ*J)) := by
  obtain ⟨J, Cd, hCd, hcnt⟩ := high_row_count rayM H hH anchors η₀ loss hloss
  refine ⟨J, fun τ hτ => ?_⟩
  obtain ⟨K₁, hK₁, S, hrow⟩ := high_row_bound rayM H hH (α := α) W hWs hW bΦ Mcap Lplain τ
    ε₁ e kap v d (by linarith) hL hτ hε₁ he he' hkap hkap' hv hd hdsupply hslotBudget
    hplainBudget
  let B : ℕ := bufferCount e
  let nb : ℕ := Fintype.card (BufferIndex e)
  have hnb : 0 < nb := Fintype.card_pos
  refine ⟨nb * (K₁*Cd*bΦ^2*(1+6*(B:ℝ))^J), by positivity, S, ?_⟩
  filter_upwards [hrow η₀, (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2)]
    with Z hZ hZτ
  refine ⟨hZ.1, hZτ, ?_⟩
  intro j q hq hq' st hchar hu hwidth hQM hQη h T θ w σ v' t height hw hw1 hσ hσ' hh0 hv'
    hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hZτ0 : 0 ≤ Z^τ := Real.rpow_nonneg hZ0.le _
  have hZτ1 : 1 ≤ Z^τ := by linarith
  set T₀ : ℝ := ((h+1 : ℕ) : ℝ)*Z^τ with hT₀def
  have hT₀ : 2 < T₀ := by
    have : (1:ℝ) ≤ ((h+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos h
    rw [hT₀def]; nlinarith
  set Pl : ℝ := length Z X₁ + length Z X₂ with hPl
  set M : ℝ := st.rowWidth with hM
  have hMc : M ≤ Mcap := by
    have := st.character_nonneg
    have : st.width = st.rowWidth + st.characterWidth := rfl
    linarith
  let sel := selectBin rayM H hH st η₀ hQM hQη e T₀
  let R : BufferIndex e → ℝ := fun c => K₁*(p.control S)^2*
    Z^((2*bufferValue e c-1)*(Pl + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1))
  let N : BufferIndex e → ℝ := fun c =>
    if (q+1)/2 ≤ bufferValue e c ∧ bufferValue e c ≤ 7/8 then
      Cd*(1+((3*c.1.val : ℕ):ℝ)*T₀)^J*(bΦ*Z^M)^(unmarkedDensity (2*bufferValue e c-1)+loss)
    else 0
  have hR : ∀ c, 0 ≤ R c := fun c => by
    have := Real.rpow_nonneg hZ0.le ((2*bufferValue e c-1)*(Pl + ∑ k, w k) +
      2*ε₁*d*(Fintype.card α + 1))
    positivity
  have hE := energy_le_classes st.character st.mask 1 t (p.profile 0) (p.profile 1)
    (fun k => primePool rayM H 2 (Z^(w k)))
    (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
    (fun k => Z^(w k)) X₁ X₂
    (fun z => st.radial.keep z ∧ ¬ lowRow rayM H hH st η₀ hQM hQη e T₀ q z)
    st.radial.profile st.radial.scale bΦ (fun z => st.radial.nonneg z) st.radial.scale_pos
    st.radial_support sel R N hR ?_ ?_
  rotate_left
  · -- pointwise bound in the chosen bin
    intro z hz hp
    obtain ⟨hk, hnl⟩ := hz
    have hbin := selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβ hβ' z hk
    have hb51 : 51/100 ≤ bufferValue e (sel z) := hbin.2.2.1
    have hb78 : bufferValue e (sel z) ≤ 7/8 := hbin.2.2.2.2.1
    have hcB : (sel z).1.val ≤ B := hbin.2.1
    have hup := hbin.2.2.2.2.2.2.2.2
    rw [hT₀def, binIndex_height] at hup
    have hwinS : ∀ k, |t + v' k| + Z^τ/2 ≤ (3*binIndex (sel z).1.val h+2 : ℕ)*Z^τ := by
      intro k
      apply window_binIndex (sel z).1.val h hZτ0
      have := abs_add_le t (v' k)
      have := hv' k
      linarith
    have hwinP : |t| + Z^τ/2 ≤ (3*binIndex (sel z).1.val h+2 : ℕ)*Z^τ := by
      apply window_binIndex (sel z).1.val h hZτ0
      linarith
    exact hZ.2 st hu hwidth hQM hQη (bufferValue e (sel z)) (binIndex (sel z).1.val h) hb51
      (by linarith) z hk hp hup T θ w σ v' t hw hw1 hσ hσ' hwinS hwinP
      (gate_binIndex (sel z).1.val h B 4 hZτ0 hcB hgate) p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  · -- the row count of each bin
    intro c rows hrows
    by_cases hc : (q+1)/2 ≤ bufferValue e c ∧ bufferValue e c ≤ 7/8
    · have hN : N c = Cd*(1+((3*c.1.val : ℕ):ℝ)*T₀)^J*
          (bΦ*Z^M)^(unmarkedDensity (2*bufferValue e c-1)+loss) := if_pos hc
      rw [hN]
      apply hcnt (by linarith : 0 < bΦ) j st hchar hu hQM hQη (bufferValue e c)
        (((3*c.1.val : ℕ):ℝ)*T₀) (by linarith [hc.1]) hc.2 (by positivity) rows
      intro z hz
      obtain ⟨⟨hk, _⟩, hp, hsel⟩ := hrows z hz
      have hbin := selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβ hβ' z hk
      change OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
        z hk e T₀ (sel z) at hbin
      rw [hsel] at hbin
      exact ⟨hk, hp, hbin.2.2.2.2.2.1⟩
    · have hN : N c = 0 := if_neg hc
      rw [hN]
      have hempty : rows = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨⟨hk, hnl⟩, _, hsel⟩ := hrows z hz
        have hbin := selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβ hβ' z hk
        have hhigh := selectBin_high rayM H hH st η₀ hQM hQη e T₀ q he hT₀ hβ hβ' z hk hnl
        change OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
          z hk e T₀ (sel z) at hbin
        change (q+1)/2 ≤ bufferValue e (sel z) at hhigh
        rw [hsel] at hbin hhigh
        exact hc ⟨hhigh, hbin.2.2.2.2.1⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero]
  -- summing over the bins
  set G : ℝ := (K₁*Cd*bΦ^2*(1+6*(B:ℝ))^J) * (p.control S)^2 * (1+|t|+height)^J *
    Z^(M + highSup q Pl (∑ k, w k) M + (2*ε₁*d*(Fintype.card α + 1) + loss*Mcap + τ*J))
    with hGdef
  have hx0 : 0 ≤ |t| + height := by positivity
  have hG0 : 0 ≤ G := by
    have := Real.rpow_nonneg hZ0.le
      (M + highSup q Pl (∑ k, w k) M + (2*ε₁*d*(Fintype.card α + 1) + loss*Mcap + τ*J))
    positivity
  have hterm : ∀ c, R c * N c ≤ G := by
    intro c
    by_cases hc : (q+1)/2 ≤ bufferValue e c ∧ bufferValue e c ≤ 7/8
    · have hN : N c = Cd*(1+((3*c.1.val : ℕ):ℝ)*T₀)^J*
          (bΦ*Z^M)^(unmarkedDensity (2*bufferValue e c-1)+loss) := if_pos hc
      rw [hN]
      set ν : ℝ := 2*bufferValue e c-1 with hν
      have hνq : q ≤ ν := by linarith [hc.1]
      have hν34 : ν ≤ 3/4 := by linarith [hc.2]
      have hν0 : 0 ≤ ν := by linarith
      have hcB : c.1.val ≤ B := Nat.lt_succ_iff.mp c.1.isLt
      have h1 : (1+((3*c.1.val : ℕ):ℝ)*T₀)^J ≤
          (1+6*(B:ℝ))^J*(1+(|t|+height))^J*(Z^τ)^J :=
        height_count_le (B := B) (c := c.1.val) (h := h) J hcB hx0 hhle hZτ1
      have h2 := density_power_le hbΦ hZ1.le hMc (unmarkedDensity_le_one hν0 hν34)
        hloss.le hloss1
      have h3 := high_exponent (P := Pl) (s := ∑ k, w k) (M := M) (by linarith) hνq hν34
      have hpow : (Z^τ)^J = Z^(τ*J) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
      have hzz : Z^(ν*(Pl + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1)) * Z^(τ*J) *
          Z^(M*unmarkedDensity ν + Mcap*loss) ≤
          Z^(M + highSup q Pl (∑ k, w k) M +
            (2*ε₁*d*(Fintype.card α + 1) + loss*Mcap + τ*J)) := by
        rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        apply Real.rpow_le_rpow_of_exponent_le hZ1.le
        nlinarith
      have hA : 0 ≤ Z^(ν*(Pl + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1)) :=
        Real.rpow_nonneg hZ0.le _
      have hB0 : 0 ≤ (1+((3*c.1.val : ℕ):ℝ)*T₀)^J := by positivity
      have hC0 : 0 ≤ (bΦ*Z^M)^(unmarkedDensity ν+loss) :=
        Real.rpow_nonneg (by positivity) _
      calc K₁*(p.control S)^2*Z^(ν*(Pl + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1)) *
            (Cd*(1+((3*c.1.val : ℕ):ℝ)*T₀)^J*(bΦ*Z^M)^(unmarkedDensity ν+loss))
          ≤ K₁*(p.control S)^2*Z^(ν*(Pl + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1)) *
            (Cd*((1+6*(B:ℝ))^J*(1+(|t|+height))^J*(Z^τ)^J)*
              (bΦ^2*Z^(M*unmarkedDensity ν + Mcap*loss))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hCd.le) h2 hC0 (by positivity)
        _ = (K₁*Cd*bΦ^2*(1+6*(B:ℝ))^J) * (p.control S)^2 * (1+|t|+height)^J *
            (Z^(ν*(Pl + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1)) * (Z^τ)^J *
              Z^(M*unmarkedDensity ν + Mcap*loss)) := by
            rw [show (1+(|t|+height)) = 1+|t|+height by ring]
            ring
        _ ≤ G := by
            rw [hGdef, hpow]
            apply mul_le_mul_of_nonneg_left hzz
            have := p.control_nonneg S
            positivity
    · have hN : N c = 0 := if_neg hc
      rw [hN, mul_zero]
      exact hG0
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  refine hE.trans ?_
  calc QuadraticInitialBound.diagonalControl st.radial.profile * ∑ c, R c * N c
      ≤ QuadraticInitialBound.diagonalControl st.radial.profile * ∑ _c : BufferIndex e, G :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hterm c)) hdiag
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hGdef]
        ring

end
end
end QRH.SilDensitySplit.Density
