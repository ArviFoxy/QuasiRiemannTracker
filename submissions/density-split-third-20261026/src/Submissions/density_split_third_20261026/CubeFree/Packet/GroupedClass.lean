/- Copyright (c) 2026 Sil. Apache-2.0.
The grouped estimate for one coefficient class (Seam B, WP-H; CF §5, common-profile lemma §1-3).

A *class* fixes everything on which the canonical packed child row depends beyond scalars:
the anchor character `σA`, the retained slot set (the slot data `S, β, P` below), the
source keep, the two source ordinary profiles `p₀, p₁` and the dyadic ordinary lengths
`Y₁, Y₂`. The children `x` of the class carry only label-dependent scalars: a weight
`ω x ≥ 0`, a packed row multiplier `V x`, a packed scale `N(V x)·K x`, and ordinary lengths
`Xᵢ x ∈ [Yᵢ/2, Yᵢ]`. Each child energy is the packed energy on the sublattice `V x · O`.

`class_bound`: if every packed scale satisfies `2 N(V x) K x ≤ Kc`, the weighted fibre at
every nonzero row `y` is `∑_{x : V x ∣ y} ω x ≤ D`, and the common rows (the source at the
ONE common scale `Kc`, `V = 1`, profiles `commonPair e τ` at `c_e Yᵢ`) satisfy the source
bound `C·pairWeight J τ·T`, then the weighted sum of the child energies is at most
`4 D · C · L₀ · L_J · T`. The proof rescales each child to the dyadic lengths
(`positiveSlotRow_rescale`, central factor `≤ 4` after squaring), restricts the lattice sums
to one finite row set, and applies `ProfileSeparation.prefix_weighted_separation`.
No bound for a label-dependent coefficient vector is used. -/
import Submissions.density_split_third_20261026.CubeFree.Packet.GroupedRows

set_option autoImplicit false

namespace QRH.DensitySplitThird.CubeFree.Packet.Grouped
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg ballProfile_le_one
  ballProfile_one)
open ProfileSeparation (dilate commonPair commonRow scale pairWeight pairMajorant)

local notation "O" => ActualEisensteinCubic.O

/-- The weighted grouped estimate of one coefficient class. -/
theorem class_bound {ι Λ : Type*} [Fintype ι] (σA : Character) (m : O) (keep : O → Prop)
    (hkeep : ∀ y, keep y → y ≠ 0)
    (p₀ p₁ : 𝓢(ℝ, ℂ)) (hs₀ : Function.support (p₀ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₁ : Function.support (p₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (Y₁ Y₂ Kc : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hKc : 0 < Kc)
    (labels : Finset Λ) (ω : Λ → ℝ) (hω : ∀ x, 0 ≤ ω x) (V : Λ → O) (K : Λ → ℝ)
    (hK : ∀ x ∈ labels, 0 < ((Ideal.span {V x}).absNorm : ℝ) * K x)
    (hscale : ∀ x ∈ labels, 2 * (((Ideal.span {V x}).absNorm : ℝ) * K x) ≤ Kc)
    (X₁ X₂ : Λ → ℝ)
    (hX : ∀ x ∈ labels, 0 < X₁ x ∧ Y₁ / 2 ≤ X₁ x ∧ X₁ x ≤ Y₁ ∧
      0 < X₂ x ∧ Y₂ / 2 ≤ X₂ x ∧ X₂ x ≤ Y₂)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ y : O, y ≠ 0 → ‖eisEmbedding y‖ ^ 2 ≤ Kc →
      ∑ x ∈ labels.filter (fun x => V x ∣ y), ω x ≤ D)
    (C T : ℝ) (J : ℕ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsource : ∀ (e : Fin 2 × Fin 2) (τ : ℝ × ℝ),
      energy σA m 1 0 ((commonPair e τ).profile 0) ((commonPair e τ).profile 1) S β P
        (scale e.1 * Y₁) (scale e.2 * Y₂) keep ballProfile Kc ≤ C * pairWeight J τ * T) :
    ∑ x ∈ labels, ω x * energy σA m 1 0 p₀ p₁ S β P (X₁ x) (X₂ x)
        (fun y => V x ∣ y ∧ keep y) ballProfile (((Ideal.span {V x}).absNorm : ℝ) * K x) ≤
      (4 * D) * C * (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ, 1 * pairMajorant p₀ p₁ hs₀ hs₁ e τ) *
        (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
          1 * pairMajorant p₀ p₁ hs₀ hs₁ e τ * pairWeight J τ) * T := by
  classical
  set Ball : Finset O := ShortDraftLatticeCount.rowNormBall ⌈2 * Kc⌉₊ with hBall
  set rows : Finset O := Ball.filter (fun y => keep y ∧ ‖eisEmbedding y‖ ^ 2 ≤ Kc) with hrows
  let ρ : Λ → ℝ := fun x => Real.sqrt (Y₁ * Y₂ / (X₁ x * X₂ x))
  let vd : Λ → ℝ × ℝ := fun x => (Real.log (Y₁ / X₁ x), Real.log (Y₂ / X₂ x))
  let B : Λ → O → ℂ := fun x y =>
    positiveSlotRow σA m 1 y (dilate p₀ (vd x).1) (dilate p₁ (vd x).2) S β P 0 Y₁ Y₂
  let bw : Λ → O → ℝ := fun x y => if V x ∣ y then
    (ballProfile (‖eisEmbedding y‖ ^ 2 / (((Ideal.span {V x}).absNorm : ℝ) * K x))).re else 0
  let w : Λ → O → ℝ := fun x y => ω x * ρ x ^ 2 * bw x y
  have hbw0 : ∀ x y, 0 ≤ bw x y := by
    intro x y
    by_cases hv : V x ∣ y
    · simp only [bw, hv, if_true]; exact ballProfile_nonneg _
    · simp only [bw, hv, if_false, le_refl]
  have hw0 : ∀ x y, 0 ≤ w x y := fun x y =>
    mul_nonneg (mul_nonneg (hω x) (sq_nonneg _)) (hbw0 x y)
  -- Step 1: each child energy is a finite row sum of rescaled rows.
  have hstep1 : ∀ x ∈ labels,
      energy σA m 1 0 p₀ p₁ S β P (X₁ x) (X₂ x) (fun y => V x ∣ y ∧ keep y) ballProfile
          (((Ideal.span {V x}).absNorm : ℝ) * K x) =
        ∑ y ∈ rows, ρ x ^ 2 * bw x y * ‖B x y‖ ^ 2 := by
    intro x hx
    obtain ⟨hX₁, hX₁l, hX₁u, hX₂, hX₂l, hX₂u⟩ := hX x hx
    unfold energy
    rw [tsum_eq_sum (s := rows)]
    · apply Finset.sum_congr rfl
      intro y hy
      have hk : keep y := (Finset.mem_filter.mp hy).2.1
      by_cases hv : V x ∣ y
      · have hc : V x ∣ y ∧ keep y := ⟨hv, hk⟩
        rw [if_pos hc]
        simp only [bw, hv, if_true]
        rw [positiveSlotRow_rescale σA m 1 y p₀ p₁ S β P 0 (X₁ x) (X₂ x) Y₁ Y₂ hX₁ hX₂ hY₁ hY₂,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        ring
      · have hc : ¬ (V x ∣ y ∧ keep y) := fun h => hv h.1
        rw [if_neg hc]
        simp only [bw, hv, if_false, mul_zero, zero_mul]
    · intro y hy
      by_cases hc : V x ∣ y ∧ keep y
      · rw [if_pos hc]
        have hb : (ballProfile (‖eisEmbedding y‖ ^ 2 /
            (((Ideal.span {V x}).absNorm : ℝ) * K x))).re = 0 := by
          by_contra hne
          have hlt := ball_lt_of_ne_zero _ _ (sq_nonneg _) (hK x hx) hne
          have hle : ‖eisEmbedding y‖ ^ 2 ≤ Kc := by linarith [hscale x hx]
          apply hy
          refine Finset.mem_filter.mpr ⟨mem_rowNormBall_of_norm_sq_le _ _ ?_, hc.2, hle⟩
          linarith
        rw [hb, mul_zero]
      · rw [if_neg hc]
  -- Step 2: swap the label and row sums.
  have hstep2 : ∑ x ∈ labels, ω x * energy σA m 1 0 p₀ p₁ S β P (X₁ x) (X₂ x)
        (fun y => V x ∣ y ∧ keep y) ballProfile (((Ideal.span {V x}).absNorm : ℝ) * K x) =
      ∑ y ∈ rows, ∑ x ∈ labels, w x y * ‖B x y‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [hstep1 x hx])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro x _
    simp only [w]; ring
  rw [hstep2]
  -- Step 3: weighted common-profile separation.
  have hvd : ∀ r ∈ rows, ∀ l ∈ (fun _ : O => labels) r,
      (vd l).1 ∈ Set.Icc 0 (Real.log 2) ∧ (vd l).2 ∈ Set.Icc 0 (Real.log 2) := by
    intro r _ l hl
    obtain ⟨hX₁, hX₁l, hX₁u, hX₂, hX₂l, hX₂u⟩ := hX l hl
    exact ⟨dilate_log_mem _ _ hX₁ hX₁l hX₁u, dilate_log_mem _ _ hX₂ hX₂l hX₂u⟩
  have hDrow : ∀ r ∈ rows, ∑ l ∈ (fun _ : O => labels) r, w l r ≤ 4 * D := by
    intro r hr
    have hk : keep r := (Finset.mem_filter.mp hr).2.1
    have hrK : ‖eisEmbedding r‖ ^ 2 ≤ Kc := (Finset.mem_filter.mp hr).2.2
    have hle : ∀ l ∈ labels, w l r ≤ 4 * (if V l ∣ r then ω l else 0) := by
      intro l hl
      obtain ⟨hX₁, hX₁l, _, hX₂, hX₂l, _⟩ := hX l hl
      have hρ := rescale_factor_le Y₁ Y₂ (X₁ l) (X₂ l) hX₁ hX₂ hX₁l hX₂l hY₁.le hY₂.le
      by_cases hv : V l ∣ r
      · simp only [w, bw, hv, if_true]
        have hb1 := ballProfile_le_one (‖eisEmbedding r‖ ^ 2 /
          (((Ideal.span {V l}).absNorm : ℝ) * K l))
        have hb0 := ballProfile_nonneg (‖eisEmbedding r‖ ^ 2 /
          (((Ideal.span {V l}).absNorm : ℝ) * K l))
        have hωl := hω l
        have h1 : ρ l ^ 2 * (ballProfile (‖eisEmbedding r‖ ^ 2 /
            (((Ideal.span {V l}).absNorm : ℝ) * K l))).re ≤ 4 :=
          by nlinarith [sq_nonneg (ρ l)]
        nlinarith
      · simp only [w, bw, hv, if_false, mul_zero, le_refl]
    calc ∑ l ∈ labels, w l r ≤ ∑ l ∈ labels, 4 * (if V l ∣ r then ω l else 0) :=
          Finset.sum_le_sum hle
      _ = 4 * ∑ x ∈ labels.filter (fun x => V x ∣ r), ω x := by
          rw [← Finset.mul_sum, Finset.sum_filter]
      _ ≤ 4 * D := by linarith [hD r (hkeep r hk) hrK]
  have hsrc : ∀ (e : Fin 2 × Fin 2) (τ : ℝ × ℝ),
      ∑ r ∈ rows, ‖commonRow σA m 1 S β P 0 Y₁ Y₂ e τ (id r)‖ ^ 2 ≤
        C * pairWeight J τ * T := by
    intro e τ
    refine le_trans ?_ (hsource e τ)
    unfold energy
    rw [tsum_eq_sum (s := Ball)]
    · calc ∑ r ∈ rows, ‖commonRow σA m 1 S β P 0 Y₁ Y₂ e τ (id r)‖ ^ 2
          = ∑ r ∈ rows, (if keep r then
              ‖positiveSlotRow σA m 1 r ((commonPair e τ).profile 0)
                ((commonPair e τ).profile 1) S β P 0 (scale e.1 * Y₁) (scale e.2 * Y₂)‖ ^ 2 *
                (ballProfile (‖eisEmbedding r‖ ^ 2 / Kc)).re else 0) := by
            apply Finset.sum_congr rfl
            intro r hr
            obtain ⟨_, hk, hle⟩ := Finset.mem_filter.mp hr
            rw [if_pos hk, ball_one_of_le _ _ (sq_nonneg _) hKc hle, mul_one]
            rfl
        _ ≤ _ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro r _ _
            split_ifs
            · exact mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)
            · exact le_refl _
    · intro r hr
      by_cases hk : keep r
      · rw [if_pos hk]
        have hb : (ballProfile (‖eisEmbedding r‖ ^ 2 / Kc)).re = 0 := by
          by_contra hne
          have hlt := ball_lt_of_ne_zero _ _ (sq_nonneg _) hKc hne
          exact hr (mem_rowNormBall_of_norm_sq_le _ _ hlt.le)
        rw [hb, mul_zero]
      · rw [if_neg hk]
  exact ProfileSeparation.prefix_weighted_separation p₀ p₁ hs₀ hs₁ σA m 1 S β P 0 Y₁ Y₂ hY₁ hY₂
    rows (fun _ => labels) id vd hvd (fun _ _ => 1) 1 zero_le_one
    (fun _ _ _ _ => by simp) B (fun r _ l _ => by simp only [B, one_mul, id]) w (4 * D) C T J
    hw0 (by linarith) hDrow hC hT hsrc

end
end QRH.DensitySplitThird.CubeFree.Packet.Grouped
