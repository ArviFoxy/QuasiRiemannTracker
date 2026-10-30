import Submissions.arvi_rip.Coherence

/-!
# Flat RIP implies RIP on a support (Bourgain–Dilworth–Ford–Konyagin–Kutzarova, Lemma 3)

Research file (QRH, RIP program). Fixed-support form: if all bilinear sums of disjoint flat
(0/1) combinations of the unit columns `u z`, `z ∈ W`, are at most `δ √(|J₁||J₂|)`, then the
columns are near-isometric on `W`, with constant `O(δ log |W|)`. Every known explicit RIP
construction beyond the square-root barrier goes through this reduction.

This file: the convexity step.
* `cube_vertex`: an affine function on the cube `[0,1]^s` attains its largest norm at a vertex.
* `flat_cube`: flat RIP on `W` bounds the bilinear sums of `[0,1]`-weighted combinations.
-/

namespace QRH.ArviRIP

open scoped BigOperators ComplexConjugate InnerProductSpace
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [DecidableEq ι]

/-- An affine function on the cube `[0,1]^s` has its largest norm at a vertex. -/
theorem cube_vertex (c : ι → ℂ) (x : ι → ℝ) {M : ℝ} (s : Finset ι)
    (hx : ∀ j ∈ s, 0 ≤ x j ∧ x j ≤ 1) :
    ∀ w : ℂ, (∀ A ⊆ s, ‖w + ∑ j ∈ A, c j‖ ≤ M) → ‖w + ∑ j ∈ s, (x j : ℂ) * c j‖ ≤ M := by
  induction s using Finset.induction_on with
  | empty => intro w h; simpa using h ∅ (Finset.empty_subset _)
  | insert a s ha ih =>
    intro w h
    have hxa := hx a (Finset.mem_insert_self a s)
    have hx' : ∀ j ∈ s, 0 ≤ x j ∧ x j ≤ 1 := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert ha]
    have hp : ‖w + ∑ j ∈ s, (x j : ℂ) * c j‖ ≤ M :=
      ih hx' w (fun A hA => h A (hA.trans (Finset.subset_insert a s)))
    have hq : ‖(w + c a) + ∑ j ∈ s, (x j : ℂ) * c j‖ ≤ M := by
      refine ih hx' (w + c a) (fun A hA => ?_)
      have hA' : insert a A ⊆ insert a s := Finset.insert_subset_insert a hA
      have haA : a ∉ A := fun h' => ha (hA h')
      have h2 := h (insert a A) hA'
      rwa [Finset.sum_insert haA, ← add_assoc] at h2
    have key : w + ((x a : ℂ) * c a + ∑ j ∈ s, (x j : ℂ) * c j) =
        ((1 - x a : ℝ) : ℂ) * (w + ∑ j ∈ s, (x j : ℂ) * c j) +
          ((x a : ℝ) : ℂ) * ((w + c a) + ∑ j ∈ s, (x j : ℂ) * c j) := by
      push_cast; ring
    have h1 : 0 ≤ 1 - x a := by linarith [hxa.2]
    rw [key]
    calc _ ≤ ‖((1 - x a : ℝ) : ℂ) * (w + ∑ j ∈ s, (x j : ℂ) * c j)‖ +
          ‖((x a : ℝ) : ℂ) * ((w + c a) + ∑ j ∈ s, (x j : ℂ) * c j)‖ := norm_add_le _ _
      _ = (1 - x a) * ‖w + ∑ j ∈ s, (x j : ℂ) * c j‖ +
          x a * ‖(w + c a) + ∑ j ∈ s, (x j : ℂ) * c j‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg h1, Real.norm_of_nonneg hxa.1]
      _ ≤ (1 - x a) * M + x a * M :=
          add_le_add (mul_le_mul_of_nonneg_left hp h1) (mul_le_mul_of_nonneg_left hq hxa.1)
      _ = M := by ring

/-- Flat RIP on a support `W`: bilinear sums of disjoint flat combinations are small. -/
def FlatOn (u : ι → E) (W : Finset ι) (δ : ℝ) : Prop :=
  ∀ J₁ ⊆ W, ∀ J₂ ⊆ W, Disjoint J₁ J₂ →
    ‖⟪∑ j ∈ J₁, u j, ∑ j ∈ J₂, u j⟫_ℂ‖ ≤ δ * Real.sqrt ((J₁.card : ℝ) * J₂.card)

/-- **Convexity step.** Flat RIP on `W` bounds bilinear sums of `[0,1]`-weighted combinations
on disjoint subsets of `W` by the same `δ √(|J₁||J₂|)`. -/
theorem flat_cube (u : ι → E) (W : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ) (hflat : FlatOn u W δ)
    (J₁ J₂ : Finset ι) (h₁ : J₁ ⊆ W) (h₂ : J₂ ⊆ W) (hd : Disjoint J₁ J₂)
    (x y : ι → ℝ) (hx : ∀ j ∈ J₁, 0 ≤ x j ∧ x j ≤ 1) (hy : ∀ j ∈ J₂, 0 ≤ y j ∧ y j ≤ 1) :
    ‖⟪∑ j ∈ J₁, (x j : ℂ) • u j, ∑ j ∈ J₂, (y j : ℂ) • u j⟫_ℂ‖ ≤
      δ * Real.sqrt ((J₁.card : ℝ) * J₂.card) := by
  set M := δ * Real.sqrt ((J₁.card : ℝ) * J₂.card)
  set v := ∑ j ∈ J₂, (y j : ℂ) • u j
  -- expand in the first slot
  have e1 : ⟪∑ j ∈ J₁, (x j : ℂ) • u j, v⟫_ℂ = 0 + ∑ j ∈ J₁, (x j : ℂ) * ⟪u j, v⟫_ℂ := by
    rw [sum_inner, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, Complex.conj_ofReal]
  rw [e1]
  refine cube_vertex (fun j => ⟪u j, v⟫_ℂ) x J₁ hx 0 (fun A hA => ?_)
  rw [zero_add, ← sum_inner]
  -- expand in the second slot
  have e2 : ⟪∑ j ∈ A, u j, v⟫_ℂ = 0 + ∑ j ∈ J₂, (y j : ℂ) * ⟪∑ i ∈ A, u i, u j⟫_ℂ := by
    rw [inner_sum, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
  rw [e2]
  refine cube_vertex (fun j => ⟪∑ i ∈ A, u i, u j⟫_ℂ) y J₂ hy 0 (fun B hB => ?_)
  rw [zero_add, ← inner_sum]
  have hAB : Disjoint A B := Finset.disjoint_of_subset_left hA (Finset.disjoint_of_subset_right hB hd)
  refine (hflat A (hA.trans h₁) B (hB.trans h₂) hAB).trans ?_
  have hcA : (A.card : ℝ) ≤ J₁.card := by exact_mod_cast Finset.card_le_card hA
  have hcB : (B.card : ℝ) ≤ J₂.card := by exact_mod_cast Finset.card_le_card hB
  have hprod : (A.card : ℝ) * B.card ≤ J₁.card * J₂.card :=
    mul_le_mul hcA hcB (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod) hδ

omit [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- Dropping the zero weights from a combination. -/
theorem sum_smul_filter [AddCommMonoid E] [Module ℂ E] (J : Finset ι) (x : ι → ℝ) (u : ι → E) :
    ∑ j ∈ J, (x j : ℂ) • u j = ∑ j ∈ J.filter (fun j => x j ≠ 0), (x j : ℂ) • u j := by
  refine (Finset.sum_filter_of_ne fun j _ h => ?_).symm
  intro hx0; apply h; simp [hx0]

/-- `flat_cube` measured by the number of nonzero weights. -/
theorem flat_cube_supp (u : ι → E) (W : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ) (hflat : FlatOn u W δ)
    (J₁ J₂ : Finset ι) (h₁ : J₁ ⊆ W) (h₂ : J₂ ⊆ W) (hd : Disjoint J₁ J₂)
    (x y : ι → ℝ) (hx : ∀ j ∈ J₁, 0 ≤ x j ∧ x j ≤ 1) (hy : ∀ j ∈ J₂, 0 ≤ y j ∧ y j ≤ 1) :
    ‖⟪∑ j ∈ J₁, (x j : ℂ) • u j, ∑ j ∈ J₂, (y j : ℂ) • u j⟫_ℂ‖ ≤
      δ * Real.sqrt (((J₁.filter (fun j => x j ≠ 0)).card : ℝ) *
        (J₂.filter (fun j => y j ≠ 0)).card) := by
  rw [sum_smul_filter J₁ x u, sum_smul_filter J₂ y u]
  refine flat_cube u W hδ hflat _ _ ((Finset.filter_subset _ _).trans h₁)
    ((Finset.filter_subset _ _).trans h₂)
    (Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hd)) x y
    (fun j hj => hx j (Finset.mem_filter.mp hj).1) (fun j hj => hy j (Finset.mem_filter.mp hj).1)

/-! ### Dyadic pieces -/

/-- Dyadic pieces of `t ∈ [0,1]`: `piece T 0 t = min t 2^{-T}` and, for `1 ≤ ν`,
`piece T ν t = min t 2^{1-ν} - min t 2^{-ν}`. -/
noncomputable def piece (T ν : ℕ) (t : ℝ) : ℝ :=
  if ν = 0 then min t ((2 : ℝ) ^ T)⁻¹ else min t ((2 : ℝ) ^ (ν - 1))⁻¹ - min t ((2 : ℝ) ^ ν)⁻¹

/-- The size bound of each piece. -/
noncomputable def scale (T ν : ℕ) : ℝ := if ν = 0 then ((2 : ℝ) ^ T)⁻¹ else ((2 : ℝ) ^ ν)⁻¹

theorem scale_pos (T ν : ℕ) : 0 < scale T ν := by
  unfold scale; split_ifs <;> positivity

theorem piece_sum (T : ℕ) {t : ℝ} (h1 : t ≤ 1) : ∑ ν ∈ range (T + 1), piece T ν t = t := by
  rw [Finset.sum_range_succ']
  have hrest : ∑ i ∈ range T, piece T (i + 1) t =
      ∑ i ∈ range T, (min t ((2 : ℝ) ^ i)⁻¹ - min t ((2 : ℝ) ^ (i + 1))⁻¹) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [piece]
  have h0 : piece T 0 t = min t ((2 : ℝ) ^ T)⁻¹ := by simp [piece]
  rw [hrest, Finset.sum_range_sub' (fun i => min t ((2 : ℝ) ^ i)⁻¹), h0]
  simp only [pow_zero, inv_one, min_eq_left h1]
  ring

theorem piece_nonneg (T ν : ℕ) {t : ℝ} (h0 : 0 ≤ t) : 0 ≤ piece T ν t := by
  unfold piece
  split_ifs with hν
  · exact le_min h0 (by positivity)
  · have hle : ((2 : ℝ) ^ ν)⁻¹ ≤ ((2 : ℝ) ^ (ν - 1))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le ν 1)
    have := min_le_min_left t hle
    linarith

theorem piece_le_scale (T ν : ℕ) {t : ℝ} (h0 : 0 ≤ t) : piece T ν t ≤ scale T ν := by
  unfold piece scale
  split_ifs with hν
  · exact min_le_right _ _
  · have h2 : ((2 : ℝ) ^ (ν - 1))⁻¹ = 2 * ((2 : ℝ) ^ ν)⁻¹ := by
      obtain ⟨k, rfl⟩ : ∃ k, ν = k + 1 := Nat.exists_eq_succ_of_ne_zero hν
      rw [Nat.add_sub_cancel, pow_succ, mul_inv]; ring
    rw [h2]
    rcases le_total t ((2 : ℝ) ^ ν)⁻¹ with h | h
    · rw [min_eq_left h, min_eq_left (by linarith [inv_nonneg.mpr (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) ν)])]
      linarith [inv_nonneg.mpr (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) ν)]
    · rw [min_eq_right h]
      have := min_le_right t (2 * ((2 : ℝ) ^ ν)⁻¹)
      linarith

theorem piece_ne_zero_lt (T ν : ℕ) (hν : ν ≠ 0) {t : ℝ} (h : piece T ν t ≠ 0) :
    ((2 : ℝ) ^ ν)⁻¹ < t := by
  by_contra hc
  push Not at hc
  apply h
  simp only [piece, hν, ↓reduceIte]
  have hle : ((2 : ℝ) ^ ν)⁻¹ ≤ ((2 : ℝ) ^ (ν - 1))⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le ν 1)
  rw [min_eq_left hc, min_eq_left (hc.trans hle)]
  ring

omit [DecidableEq ι] in
/-- Chebyshev: at most `4^ν ∑ x²` weights exceed `2^{-ν}`. -/
theorem card_level_le (J : Finset ι) (x : ι → ℝ) (ν : ℕ) :
    ((J.filter (fun j => ((2 : ℝ) ^ ν)⁻¹ < x j)).card : ℝ) ≤ 4 ^ ν * ∑ j ∈ J, x j ^ 2 := by
  classical
  calc ((J.filter (fun j => ((2 : ℝ) ^ ν)⁻¹ < x j)).card : ℝ)
      = ∑ j ∈ J.filter (fun j => ((2 : ℝ) ^ ν)⁻¹ < x j), (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ J.filter (fun j => ((2 : ℝ) ^ ν)⁻¹ < x j), 4 ^ ν * x j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := (Finset.mem_filter.mp hj).2
        have hp : (0 : ℝ) < 2 ^ ν := by positivity
        have h1 : 1 < 2 ^ ν * x j := by
          rw [inv_lt_iff_one_lt_mul₀ hp] at hj'; linarith
        have h4 : (4 : ℝ) ^ ν = (2 ^ ν) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [h4]; nlinarith
    _ ≤ ∑ j ∈ J, 4 ^ ν * x j ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => by positivity)
    _ = 4 ^ ν * ∑ j ∈ J, x j ^ 2 := by rw [Finset.mul_sum]

omit [DecidableEq ι] in
/-- Each piece is supported on few indices at its scale: `scale · √(#support) ≤ ‖x‖₂` for the
levels `ν ≥ 1`, and `≤ 2^{-T} √|J|` for the tail `ν = 0`. -/
theorem scaled_count (T ν : ℕ) (J : Finset ι) (x : ι → ℝ) :
    scale T ν * Real.sqrt ((J.filter (fun j => piece T ν (x j) ≠ 0)).card) ≤
      (if ν = 0 then ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J.card else Real.sqrt (∑ j ∈ J, x j ^ 2)) := by
  classical
  split_ifs with hν
  · simp only [scale, hν, ↓reduceIte]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  · simp only [scale, hν, ↓reduceIte]
    have hsub : J.filter (fun j => piece T ν (x j) ≠ 0) ⊆
        J.filter (fun j => ((2 : ℝ) ^ ν)⁻¹ < x j) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, piece_ne_zero_lt T ν hν hj.2⟩
    have hc0 : ((J.filter (fun j => piece T ν (x j) ≠ 0)).card : ℝ) ≤
        ((J.filter (fun j => ((2 : ℝ) ^ ν)⁻¹ < x j)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hc := hc0.trans (card_level_le J x ν)
    have h4 : Real.sqrt (4 ^ ν * ∑ j ∈ J, x j ^ 2) = 2 ^ ν * Real.sqrt (∑ j ∈ J, x j ^ 2) := by
      have e : (4 : ℝ) ^ ν = (2 ^ ν) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [Real.sqrt_mul (by positivity), e, Real.sqrt_sq (by positivity)]
    calc ((2 : ℝ) ^ ν)⁻¹ * Real.sqrt ((J.filter (fun j => piece T ν (x j) ≠ 0)).card)
        ≤ ((2 : ℝ) ^ ν)⁻¹ * Real.sqrt (4 ^ ν * ∑ j ∈ J, x j ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (by positivity)
      _ = Real.sqrt (∑ j ∈ J, x j ^ 2) := by
          rw [h4, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

omit [DecidableEq ι] in
/-- Sum of the scaled counts over all pieces. -/
theorem sum_scaled_count (T : ℕ) (J : Finset ι) (x : ι → ℝ) :
    ∑ ν ∈ range (T + 1), scale T ν * Real.sqrt ((J.filter (fun j => piece T ν (x j) ≠ 0)).card) ≤
      T * Real.sqrt (∑ j ∈ J, x j ^ 2) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J.card := by
  rw [Finset.sum_range_succ']
  have h0 := scaled_count T 0 J x
  simp only [↓reduceIte] at h0
  have hrest : ∑ i ∈ range T, scale T (i + 1) *
      Real.sqrt ((J.filter (fun j => piece T (i + 1) (x j) ≠ 0)).card) ≤
        ∑ _i ∈ range T, Real.sqrt (∑ j ∈ J, x j ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h := scaled_count T (i + 1) J x
    simpa using h
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hrest
  linarith

/-- **Dyadic step.** Flat RIP on `W` bounds the bilinear sums of nonnegative combinations with
weights `≤ 1` on disjoint `J₁, J₂ ⊆ W` by `δ (T‖x‖ + 2^{-T}√|J₁|)(T‖y‖ + 2^{-T}√|J₂|)`. -/
theorem flat_dyadic (u : ι → E) (W : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ) (hflat : FlatOn u W δ)
    (J₁ J₂ : Finset ι) (h₁ : J₁ ⊆ W) (h₂ : J₂ ⊆ W) (hd : Disjoint J₁ J₂)
    (x y : ι → ℝ) (hx : ∀ j ∈ J₁, 0 ≤ x j ∧ x j ≤ 1) (hy : ∀ j ∈ J₂, 0 ≤ y j ∧ y j ≤ 1)
    (T : ℕ) :
    ‖⟪∑ j ∈ J₁, (x j : ℂ) • u j, ∑ j ∈ J₂, (y j : ℂ) • u j⟫_ℂ‖ ≤
      δ * ((T * Real.sqrt (∑ j ∈ J₁, x j ^ 2) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J₁.card) *
        (T * Real.sqrt (∑ j ∈ J₂, y j ^ 2) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J₂.card)) := by
  have dec : ∀ (J : Finset ι) (z : ι → ℝ), (∀ j ∈ J, 0 ≤ z j ∧ z j ≤ 1) →
      ∑ j ∈ J, (z j : ℂ) • u j =
        ∑ ν ∈ range (T + 1), ∑ j ∈ J, (piece T ν (z j) : ℂ) • u j := by
    intro J z hz
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, piece_sum T (hz j hj).2]
  set A : ℕ → ℝ := fun ν =>
    scale T ν * Real.sqrt ((J₁.filter (fun j => piece T ν (x j) ≠ 0)).card) with hA
  set B : ℕ → ℝ := fun μ =>
    scale T μ * Real.sqrt ((J₂.filter (fun j => piece T μ (y j) ≠ 0)).card) with hB
  have norm_scaled : ∀ (J : Finset ι) (z : ι → ℝ) (ν : ℕ),
      ∑ j ∈ J, (piece T ν (z j) : ℂ) • u j =
        (scale T ν : ℂ) • ∑ j ∈ J, ((piece T ν (z j) / scale T ν : ℝ) : ℂ) • u j := by
    intro J z ν
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    congr 1
    have h' : (scale T ν : ℂ) ≠ 0 := by exact_mod_cast (scale_pos T ν).ne'
    push_cast
    field_simp
  have filt : ∀ (J : Finset ι) (z : ι → ℝ) (ν : ℕ),
      J.filter (fun j => piece T ν (z j) / scale T ν ≠ 0) =
        J.filter (fun j => piece T ν (z j) ≠ 0) := by
    intro J z ν
    ext j
    simp [(scale_pos T ν).ne']
  have hpair : ∀ ν μ, ‖⟪∑ j ∈ J₁, (piece T ν (x j) : ℂ) • u j,
      ∑ j ∈ J₂, (piece T μ (y j) : ℂ) • u j⟫_ℂ‖ ≤ δ * (A ν * B μ) := by
    intro ν μ
    have hsν := scale_pos T ν
    have hsμ := scale_pos T μ
    rw [norm_scaled J₁ x ν, norm_scaled J₂ y μ, inner_smul_left, inner_smul_right, norm_mul,
      norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hsν.le, Real.norm_of_nonneg hsμ.le]
    have hb := flat_cube_supp u W hδ hflat J₁ J₂ h₁ h₂ hd
      (fun j => piece T ν (x j) / scale T ν) (fun j => piece T μ (y j) / scale T μ)
      (fun j hj => ⟨div_nonneg (piece_nonneg T ν (hx j hj).1) hsν.le,
        (div_le_one hsν).mpr (piece_le_scale T ν (hx j hj).1)⟩)
      (fun j hj => ⟨div_nonneg (piece_nonneg T μ (hy j hj).1) hsμ.le,
        (div_le_one hsμ).mpr (piece_le_scale T μ (hy j hj).1)⟩)
    rw [filt J₁ x ν, filt J₂ y μ] at hb
    calc scale T ν * (scale T μ * ‖⟪∑ j ∈ J₁, ((piece T ν (x j) / scale T ν : ℝ) : ℂ) • u j,
          ∑ j ∈ J₂, ((piece T μ (y j) / scale T μ : ℝ) : ℂ) • u j⟫_ℂ‖)
        ≤ scale T ν * (scale T μ * (δ * Real.sqrt
            (((J₁.filter (fun j => piece T ν (x j) ≠ 0)).card : ℝ) *
              (J₂.filter (fun j => piece T μ (y j) ≠ 0)).card))) := by
          gcongr
      _ = δ * (A ν * B μ) := by
          rw [hA, hB, Real.sqrt_mul (Nat.cast_nonneg _)]
          ring
  rw [dec J₁ x hx, dec J₂ y hy, sum_inner]
  have hAnn : ∀ ν, 0 ≤ A ν := fun ν => mul_nonneg (scale_pos T ν).le (Real.sqrt_nonneg _)
  have hBnn : ∀ μ, 0 ≤ B μ := fun μ => mul_nonneg (scale_pos T μ).le (Real.sqrt_nonneg _)
  calc ‖∑ ν ∈ range (T + 1), ⟪∑ j ∈ J₁, (piece T ν (x j) : ℂ) • u j,
        ∑ μ ∈ range (T + 1), ∑ j ∈ J₂, (piece T μ (y j) : ℂ) • u j⟫_ℂ‖
      ≤ ∑ ν ∈ range (T + 1), ∑ μ ∈ range (T + 1), δ * (A ν * B μ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
        rw [inner_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => hpair ν μ)
    _ = δ * ((∑ ν ∈ range (T + 1), A ν) * (∑ μ ∈ range (T + 1), B μ)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact mul_le_mul (sum_scaled_count T J₁ x) (sum_scaled_count T J₂ y)
          (Finset.sum_nonneg fun μ _ => hBnn μ) (by positivity)

/-- The constant of the dyadic step once the weights are normalized. -/
noncomputable def dyc (T : ℕ) (W : Finset ι) : ℝ := (T + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt W.card) ^ 2

omit [DecidableEq ι] in
theorem dyc_nonneg (T : ℕ) (W : Finset ι) : 0 ≤ dyc T W := sq_nonneg _

omit [DecidableEq ι] in
theorem le_sqrt_sum_sq {J : Finset ι} {x : ι → ℝ} {j : ι} (hj : j ∈ J) (h0 : 0 ≤ x j) :
    x j ≤ Real.sqrt (∑ i ∈ J, x i ^ 2) := by
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun i _ => sq_nonneg (x i)) hj)

omit [DecidableEq ι] in
theorem eq_zero_of_sqrt_sum_sq {J : Finset ι} {x : ι → ℝ}
    (h : Real.sqrt (∑ i ∈ J, x i ^ 2) = 0) : ∀ j ∈ J, x j = 0 := by
  intro j hj
  have hs : ∑ i ∈ J, x i ^ 2 = 0 := by
    have h1 := Real.sqrt_eq_zero'.mp h
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ J) => sq_nonneg (x i))]
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp hs j hj
  exact pow_eq_zero_iff two_ne_zero |>.mp h2

omit [DecidableEq ι] in
theorem smul_sum_div (J : Finset ι) (x : ι → ℝ) (u : ι → E) {c : ℝ} (_hc : c ≠ 0) :
    ∑ j ∈ J, ((x j / c : ℝ) : ℂ) • u j = ((c⁻¹ : ℝ) : ℂ) • ∑ j ∈ J, (x j : ℂ) • u j := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- **Nonnegative weights of any size.** -/
theorem flat_nonneg (u : ι → E) (W : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ) (hflat : FlatOn u W δ)
    (J₁ J₂ : Finset ι) (h₁ : J₁ ⊆ W) (h₂ : J₂ ⊆ W) (hd : Disjoint J₁ J₂)
    (x y : ι → ℝ) (hx : ∀ j ∈ J₁, 0 ≤ x j) (hy : ∀ j ∈ J₂, 0 ≤ y j) (T : ℕ) :
    ‖⟪∑ j ∈ J₁, (x j : ℂ) • u j, ∑ j ∈ J₂, (y j : ℂ) • u j⟫_ℂ‖ ≤
      δ * dyc T W * (Real.sqrt (∑ j ∈ J₁, x j ^ 2) * Real.sqrt (∑ j ∈ J₂, y j ^ 2)) := by
  set nx := Real.sqrt (∑ j ∈ J₁, x j ^ 2) with hnxdef
  set ny := Real.sqrt (∑ j ∈ J₂, y j ^ 2) with hnydef
  have hR : 0 ≤ δ * dyc T W := mul_nonneg hδ (dyc_nonneg T W)
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (∑ j ∈ J₁, x j ^ 2)) with hnx | hnx
  · have hx0 := eq_zero_of_sqrt_sum_sq hnx.symm
    have hS : ∑ j ∈ J₁, (x j : ℂ) • u j = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hx0 j hj]
    rw [hS, inner_zero_left, norm_zero]
    exact mul_nonneg hR (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (∑ j ∈ J₂, y j ^ 2)) with hny | hny
  · have hy0 := eq_zero_of_sqrt_sum_sq hny.symm
    have hS : ∑ j ∈ J₂, (y j : ℂ) • u j = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hy0 j hj]
    rw [hS, inner_zero_right, norm_zero]
    exact mul_nonneg hR (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsx : ∑ j ∈ J₁, (x j / nx) ^ 2 = 1 := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, hnxdef, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
    have : (0 : ℝ) < ∑ j ∈ J₁, x j ^ 2 := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg fun i (_ : i ∈ J₁) => sq_nonneg (x i)) with h | h
      · exact h
      · exfalso; rw [← h, Real.sqrt_zero] at hnx; exact lt_irrefl 0 hnx
    exact div_self this.ne'
  have hsy : ∑ j ∈ J₂, (y j / ny) ^ 2 = 1 := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, hnydef, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (y i))]
    have : (0 : ℝ) < ∑ j ∈ J₂, y j ^ 2 := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg fun i (_ : i ∈ J₂) => sq_nonneg (y i)) with h | h
      · exact h
      · exfalso; rw [← h, Real.sqrt_zero] at hny; exact lt_irrefl 0 hny
    exact div_self this.ne'
  have key := flat_dyadic u W hδ hflat J₁ J₂ h₁ h₂ hd (fun j => x j / nx) (fun j => y j / ny)
    (fun j hj => ⟨div_nonneg (hx j hj) hnx.le, (div_le_one hnx).mpr (le_sqrt_sum_sq hj (hx j hj))⟩)
    (fun j hj => ⟨div_nonneg (hy j hj) hny.le, (div_le_one hny).mpr (le_sqrt_sum_sq hj (hy j hj))⟩) T
  simp only [hsx, hsy, Real.sqrt_one, mul_one] at key
  rw [smul_sum_div J₁ x u hnx.ne', smul_sum_div J₂ y u hny.ne', inner_smul_left, inner_smul_right,
    norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hnx.le), Real.norm_of_nonneg (inv_nonneg.mpr hny.le)] at key
  have hW1 : Real.sqrt J₁.card ≤ Real.sqrt W.card :=
    Real.sqrt_le_sqrt (by exact_mod_cast Finset.card_le_card h₁)
  have hW2 : Real.sqrt J₂.card ≤ Real.sqrt W.card :=
    Real.sqrt_le_sqrt (by exact_mod_cast Finset.card_le_card h₂)
  have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hfac : ((T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J₁.card) *
      ((T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J₂.card) ≤ dyc T W := by
    unfold dyc
    rw [sq]
    have a1 : (T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J₁.card ≤
        (T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt W.card := by gcongr
    have a2 : (T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt J₂.card ≤
        (T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt W.card := by gcongr
    exact mul_le_mul a1 a2 (by positivity) (by positivity)
  set I := ‖⟪∑ j ∈ J₁, (x j : ℂ) • u j, ∑ j ∈ J₂, (y j : ℂ) • u j⟫_ℂ‖
  have key' : I ≤ nx * ny * (δ * dyc T W) := by
    have h3 : nx⁻¹ * (ny⁻¹ * I) ≤ δ * dyc T W := key.trans (mul_le_mul_of_nonneg_left hfac hδ)
    have hnx0 : nx ≠ 0 := hnx.ne'
    have hny0 : ny ≠ 0 := hny.ne'
    have h4 : I = nx * ny * (nx⁻¹ * (ny⁻¹ * I)) := by field_simp
    rw [h4]
    exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hnx.le hny.le)
  calc I ≤ nx * ny * (δ * dyc T W) := key'
    _ = δ * dyc T W * (nx * ny) := by ring

/-! ### Complex weights -/

/-- The four nonnegative parts of a complex number, `a = r⁺ - r⁻ + i (s⁺ - s⁻)`. -/
noncomputable def part : Fin 4 → ℂ → ℝ
  | 0, a => max a.re 0
  | 1, a => max (-a.re) 0
  | 2, a => max a.im 0
  | 3, a => max (-a.im) 0

/-- The unimodular coefficients of the four parts. -/
def pcoef : Fin 4 → ℂ
  | 0 => 1
  | 1 => -1
  | 2 => Complex.I
  | 3 => -Complex.I

theorem part_decomp (a : ℂ) : ∑ k : Fin 4, pcoef k * (part k a : ℂ) = a := by
  have h1 := max_zero_sub_max_neg_zero_eq_self a.re
  have h2 := max_zero_sub_max_neg_zero_eq_self a.im
  rw [Fin.sum_univ_four]
  calc pcoef 0 * (part 0 a : ℂ) + pcoef 1 * (part 1 a : ℂ) + pcoef 2 * (part 2 a : ℂ) +
        pcoef 3 * (part 3 a : ℂ)
      = ((max a.re 0 - max (-a.re) 0 : ℝ) : ℂ) +
          ((max a.im 0 - max (-a.im) 0 : ℝ) : ℂ) * Complex.I := by
        simp only [part, pcoef]; push_cast; ring
    _ = a := by rw [h1, h2, Complex.re_add_im]

theorem part_nonneg (k : Fin 4) (a : ℂ) : 0 ≤ part k a := by
  fin_cases k <;> simp [part]

theorem part_le_norm (k : Fin 4) (a : ℂ) : part k a ≤ ‖a‖ := by
  have hr := Complex.abs_re_le_norm a
  have hi := Complex.abs_im_le_norm a
  have hn := norm_nonneg a
  fin_cases k <;> simp only [part] <;> refine max_le ?_ hn
  · exact (le_abs_self _).trans hr
  · exact (neg_le_abs _).trans hr
  · exact (le_abs_self _).trans hi
  · exact (neg_le_abs _).trans hi

theorem pcoef_norm (k : Fin 4) : ‖pcoef k‖ = 1 := by
  fin_cases k <;> simp [pcoef]

omit [DecidableEq ι] in
theorem sum_decomp (J : Finset ι) (a : ι → ℂ) (u : ι → E) :
    ∑ j ∈ J, a j • u j = ∑ k : Fin 4, pcoef k • ∑ j ∈ J, (part k (a j) : ℂ) • u j := by
  have h : ∀ j, a j • u j = ∑ k : Fin 4, pcoef k • ((part k (a j) : ℂ) • u j) := by
    intro j
    conv_lhs => rw [← part_decomp (a j)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp_rw [Finset.smul_sum]

/-- **Complex weights.** -/
theorem flat_complex (u : ι → E) (W : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ) (hflat : FlatOn u W δ)
    (J₁ J₂ : Finset ι) (h₁ : J₁ ⊆ W) (h₂ : J₂ ⊆ W) (hd : Disjoint J₁ J₂) (a b : ι → ℂ)
    (T : ℕ) :
    ‖⟪∑ j ∈ J₁, a j • u j, ∑ j ∈ J₂, b j • u j⟫_ℂ‖ ≤
      16 * (δ * dyc T W) *
        (Real.sqrt (∑ j ∈ J₁, ‖a j‖ ^ 2) * Real.sqrt (∑ j ∈ J₂, ‖b j‖ ^ 2)) := by
  set K := δ * dyc T W with hK
  have hK0 : 0 ≤ K := mul_nonneg hδ (dyc_nonneg T W)
  have hpa : ∀ k, Real.sqrt (∑ j ∈ J₁, part k (a j) ^ 2) ≤ Real.sqrt (∑ j ∈ J₁, ‖a j‖ ^ 2) :=
    fun k => Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (part_nonneg k _) (part_le_norm k _) 2)
  have hpb : ∀ k, Real.sqrt (∑ j ∈ J₂, part k (b j) ^ 2) ≤ Real.sqrt (∑ j ∈ J₂, ‖b j‖ ^ 2) :=
    fun k => Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (part_nonneg k _) (part_le_norm k _) 2)
  rw [sum_decomp J₁ a u, sum_decomp J₂ b u, sum_inner]
  calc _ ≤ ∑ _k : Fin 4, ∑ _l : Fin 4, K *
        (Real.sqrt (∑ j ∈ J₁, ‖a j‖ ^ 2) * Real.sqrt (∑ j ∈ J₂, ‖b j‖ ^ 2)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [inner_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, Complex.norm_conj, pcoef_norm,
          pcoef_norm, one_mul, one_mul]
        refine (flat_nonneg u W hδ hflat J₁ J₂ h₁ h₂ hd _ _ (fun j _ => part_nonneg k (a j))
          (fun j _ => part_nonneg l (b j)) T).trans ?_
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hpa k) (hpb l) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hK0
    _ = 16 * K * (Real.sqrt (∑ j ∈ J₁, ‖a j‖ ^ 2) * Real.sqrt (∑ j ∈ J₂, ‖b j‖ ^ 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ### Averaging over splittings -/

/-- For `z ≠ z'` in `W`, a quarter of the subsets of `W` contain `z` and miss `z'`. -/
theorem count_split {W : Finset ι} {z z' : ι} (hz : z ∈ W) (hz' : z' ∈ W) (hne : z ≠ z') :
    4 * (W.powerset.filter (fun J => z ∈ J ∧ z' ∉ J)).card = 2 ^ W.card := by
  set W₀ := (W.erase z).erase z' with hW₀
  have hz'e : z' ∈ W.erase z := Finset.mem_erase.mpr ⟨Ne.symm hne, hz'⟩
  have hcard : W.card = W₀.card + 2 := by
    have e1 := Finset.card_erase_of_mem hz'e
    have e2 := Finset.card_erase_of_mem hz
    have hpos : 1 ≤ (W.erase z).card := Finset.card_pos.mpr ⟨z', hz'e⟩
    have hpos' : 1 ≤ W.card := Finset.card_pos.mpr ⟨z, hz⟩
    rw [hW₀]; omega
  have hbij : (W.powerset.filter (fun J => z ∈ J ∧ z' ∉ J)).card = W₀.powerset.card := by
    apply Finset.card_nbij' (fun J => (J.erase z)) (fun K => insert z K)
    · intro J hJ
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hJ
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
      intro x hx
      rw [hW₀, Finset.mem_erase, Finset.mem_erase]
      have hxJ := (Finset.mem_erase.mp hx).2
      refine ⟨?_, (Finset.mem_erase.mp hx).1, hJ.1 hxJ⟩
      rintro rfl; exact hJ.2.2 hxJ
    · intro K hK
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset] at hK
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq]
      refine ⟨?_, Finset.mem_insert_self z K, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hz
        · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hK hx))
      · intro hz'K
        rcases Finset.mem_insert.mp hz'K with h | h
        · exact hne h.symm
        · have := hK h
          rw [hW₀, Finset.mem_erase] at this
          exact this.1 rfl
    · intro J hJ
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hJ
      exact Finset.insert_erase hJ.2.1
    · intro K hK
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset] at hK
      have hzK : z ∉ K := by
        intro h
        have := hK h
        rw [hW₀, Finset.mem_erase, Finset.mem_erase] at this
        exact this.2.1 rfl
      exact Finset.erase_insert hzK
  rw [hbij, Finset.card_powerset, hcard, pow_add]
  ring

/-- Splitting identity: `4 ∑_{J ⊆ W} ∑_{z ∈ J} ∑_{z' ∈ W \ J} g z z' = 2^{|W|} ∑_{z ≠ z'} g z z'`. -/
theorem avg_identity (W : Finset ι) (g : ι → ι → ℂ) :
    4 * ∑ J ∈ W.powerset, ∑ z ∈ J, ∑ z' ∈ W \ J, g z z' =
      2 ^ W.card * ∑ z ∈ W, ∑ z' ∈ W.erase z, g z z' := by
  have h1 : ∀ J ∈ W.powerset, ∑ z ∈ J, ∑ z' ∈ W \ J, g z z' =
      ∑ z ∈ W, ∑ z' ∈ W, if z ∈ J ∧ z' ∉ J then g z z' else 0 := by
    intro J hJ
    have hJW : J ⊆ W := Finset.mem_powerset.mp hJ
    have e1 : ∀ z, ∑ z' ∈ W \ J, g z z' = ∑ z' ∈ W, if z' ∉ J then g z z' else 0 := by
      intro z
      rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    have e2 : ∑ z ∈ J, ∑ z' ∈ W \ J, g z z' =
        ∑ z ∈ W, if z ∈ J then ∑ z' ∈ W \ J, g z z' else 0 := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hJW]
    rw [e2]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [e1 z]
    split_ifs with hzJ
    · refine Finset.sum_congr rfl fun z' _ => ?_
      simp [hzJ]
    · simp [hzJ]
  set c : ι → ι → ℂ := fun z z' =>
    ((W.powerset.filter (fun J => z ∈ J ∧ z' ∉ J)).card : ℂ) with hc
  have h2 : ∑ J ∈ W.powerset, ∑ z ∈ W, ∑ z' ∈ W, (if z ∈ J ∧ z' ∉ J then g z z' else 0) =
      ∑ z ∈ W, ∑ z' ∈ W, g z z' * c z z' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : ∀ z ∈ W, (∑ z' ∈ W, g z z' * c z z') * 4 = 2 ^ W.card * ∑ z' ∈ W.erase z, g z z' := by
    intro z hz
    rw [Finset.sum_mul, ← Finset.add_sum_erase W _ hz]
    have hdiag : c z z = 0 := by
      rw [hc]
      simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro J _ h
      exact h.2 h.1
    rw [hdiag, mul_zero, zero_mul, zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z' hz' => ?_
    have hne : z ≠ z' := (Finset.ne_of_mem_erase hz').symm
    have hz'W : z' ∈ W := Finset.mem_of_mem_erase hz'
    have hcount := count_split hz hz'W hne
    have hc' : c z z' * 4 = (2 : ℂ) ^ W.card := by
      simp only [hc]
      rw [mul_comm]
      exact_mod_cast hcount
    rw [mul_assoc, hc']
    ring
  calc 4 * ∑ J ∈ W.powerset, ∑ z ∈ J, ∑ z' ∈ W \ J, g z z'
      = 4 * ∑ J ∈ W.powerset, ∑ z ∈ W, ∑ z' ∈ W,
          (if z ∈ J ∧ z' ∉ J then g z z' else 0) := by
        rw [Finset.sum_congr rfl h1]
    _ = 4 * ∑ z ∈ W, ∑ z' ∈ W, g z z' * c z z' := by rw [h2]
    _ = ∑ z ∈ W, (∑ z' ∈ W, g z z' * c z z') * 4 := by
        rw [mul_comm, Finset.sum_mul]
    _ = ∑ z ∈ W, 2 ^ W.card * ∑ z' ∈ W.erase z, g z z' := Finset.sum_congr rfl h3
    _ = 2 ^ W.card * ∑ z ∈ W, ∑ z' ∈ W.erase z, g z z' := by rw [Finset.mul_sum]

/-- **Flat RIP implies near-isometry on the support** (BDFKK Lemma 3, fixed-support form).
If the unit columns `u z`, `z ∈ W`, have flat RIP constant `δ` on `W`, then for every `T`,
`|‖∑ a z u z‖² - ∑ |a z|²| ≤ 32 δ (T + 2^{-T} √|W|)² ∑ |a z|²`. Taking `2^T ≥ √|W|` gives
`32 δ (T + 1)²` with `T ≈ log₂ √|W|`. -/
theorem flat_rip_on (u : ι → E) (W : Finset ι) (hu : ∀ z ∈ W, ‖u z‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hflat : FlatOn u W δ) (T : ℕ) (a : ι → ℂ) :
    |‖∑ z ∈ W, a z • u z‖ ^ 2 - ∑ z ∈ W, ‖a z‖ ^ 2| ≤
      32 * (δ * dyc T W) * ∑ z ∈ W, ‖a z‖ ^ 2 := by
  set K := δ * dyc T W with hK
  have hK0 : 0 ≤ K := mul_nonneg hδ (dyc_nonneg T W)
  set O := ∑ z ∈ W, ∑ z' ∈ W.erase z, conj (a z) * a z' * ⟪u z, u z'⟫_ℂ with hO
  have hre : ‖∑ z ∈ W, a z • u z‖ ^ 2 - ∑ z ∈ W, ‖a z‖ ^ 2 = O.re := by
    have h := congrArg Complex.re (gram_split W a u hu)
    rw [← hO, Complex.add_re, Complex.ofReal_re] at h
    rw [norm_sq_eq_re, h]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm O).trans ?_
  set A := ∑ z ∈ W, ‖a z‖ ^ 2 with hA
  -- each splitting is small
  have hsplit : ∀ J ∈ W.powerset,
      ‖∑ z ∈ J, ∑ z' ∈ W \ J, conj (a z) * a z' * ⟪u z, u z'⟫_ℂ‖ ≤ 8 * K * A := by
    intro J hJ
    have hJW : J ⊆ W := Finset.mem_powerset.mp hJ
    have hexp : ∑ z ∈ J, ∑ z' ∈ W \ J, conj (a z) * a z' * ⟪u z, u z'⟫_ℂ =
        ⟪∑ z ∈ J, a z • u z, ∑ z' ∈ W \ J, a z' • u z'⟫_ℂ := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [inner_smul_left, inner_smul_right]
      ring
    rw [hexp]
    refine (flat_complex u W hδ hflat J (W \ J) hJW Finset.sdiff_subset
      Finset.disjoint_sdiff a a T).trans ?_
    set p := ∑ z ∈ J, ‖a z‖ ^ 2
    set q := ∑ z ∈ W \ J, ‖a z‖ ^ 2
    have hpq : p + q = A := by
      rw [hA, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hJW]
    have hp : 0 ≤ p := Finset.sum_nonneg fun z _ => sq_nonneg _
    have hq : 0 ≤ q := Finset.sum_nonneg fun z _ => sq_nonneg _
    have amgm : Real.sqrt p * Real.sqrt q ≤ A / 2 := by
      have h := Real.sqrt_mul_self hp
      have h' := Real.sqrt_mul_self hq
      nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q), Real.sqrt_nonneg p, Real.sqrt_nonneg q,
        Real.sq_sqrt hp, Real.sq_sqrt hq]
    calc 16 * K * (Real.sqrt p * Real.sqrt q) ≤ 16 * K * (A / 2) :=
          mul_le_mul_of_nonneg_left amgm (by positivity)
      _ = 8 * K * A := by ring
  -- averaging
  have hid := avg_identity W (fun z z' => conj (a z) * a z' * ⟪u z, u z'⟫_ℂ)
  rw [← hO] at hid
  have hpow : (0 : ℝ) < 2 ^ W.card := by positivity
  have hnorm : (2 : ℝ) ^ W.card * ‖O‖ ≤ 4 * ((2 : ℝ) ^ W.card * (8 * K * A)) := by
    have e : ‖(2 : ℂ) ^ W.card * O‖ = (2 : ℝ) ^ W.card * ‖O‖ := by
      rw [norm_mul, norm_pow, Complex.norm_two]
    rw [← e, ← hid, norm_mul, Complex.norm_ofNat]
    gcongr
    refine (norm_sum_le _ _).trans ?_
    calc ∑ J ∈ W.powerset, ‖∑ z ∈ J, ∑ z' ∈ W \ J, conj (a z) * a z' * ⟪u z, u z'⟫_ℂ‖
        ≤ ∑ _J ∈ W.powerset, 8 * K * A := Finset.sum_le_sum hsplit
      _ = (2 : ℝ) ^ W.card * (8 * K * A) := by
          rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]; push_cast; ring
  have : ‖O‖ ≤ 4 * (8 * K * A) := by
    have h2 : (2 : ℝ) ^ W.card * ‖O‖ ≤ (2 : ℝ) ^ W.card * (4 * (8 * K * A)) := by linarith
    exact le_of_mul_le_mul_left h2 hpow
  linarith

end QRH.ArviRIP

#print axioms QRH.ArviRIP.flat_cube
#print axioms QRH.ArviRIP.piece_sum
#print axioms QRH.ArviRIP.card_level_le
#print axioms QRH.ArviRIP.flat_dyadic
#print axioms QRH.ArviRIP.flat_nonneg
#print axioms QRH.ArviRIP.flat_rip_on
