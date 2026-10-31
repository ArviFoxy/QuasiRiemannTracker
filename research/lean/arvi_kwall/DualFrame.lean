import Mathlib

/-!
# The dual-frame (Q-metric) bound

Research file (QRH, RIP program (4); the "dual-frame" tie of the journal's fresh look).

Rows are indexed by a finite type `ρ`; row vectors are `y : ρ → ℂ`, with `⟨u, w⟩ = ∑_z conj (u z) * w z`
(Lean: `star u ⬝ᵥ w`). Let `Q` be a positive definite Hermitian matrix on the row space. For a row subset
`W` put

  `c_W(Q) = sup { Re⟨v, Q⁻¹ v⟩ : v supported on W, ‖v‖ = 1 }`   (`cW`).

Then for every row vector `y`

  `∑_{z∈W} |y z|² ≤ c_W(Q) · ⟨y, Q y⟩`   (`dual_frame_bound`).

The proof is Cauchy–Schwarz for the positive semidefinite form `(u, w) ↦ ⟨u, Q w⟩`:
`|⟨v, y⟩|² ≤ ⟨v, Q⁻¹ v⟩ ⟨y, Q y⟩` (`dual_cauchy_schwarz`), applied to `v = P_W y`, the restriction of `y`
to `W`.

* `qform_cauchy_schwarz`: Cauchy–Schwarz for the form of a positive semidefinite matrix.
* `dual_cauchy_schwarz`: `|⟨v, y⟩|² ≤ ⟨v, P v⟩ ⟨y, Q y⟩` whenever `Q ⪰ 0` and `Q P = 1`.
* `dual_frame_bound_of_le`: the bound with any constant `c ≥ 0` that bounds the dual form on `W`.
* `dual_frame_bound`: the bound with `c = c_W(Q)`.
* `dual_frame_large_sieve`: for `y = M a`, if `⟨M a, Q M a⟩ ≤ λ ‖a‖²` for all `a`, then on every row subset
  `∑_{z∈W} |(M a) z|² ≤ c_W(Q) · λ · ‖a‖²`.
* `cW_one_eq`, `dual_frame_bound_one`, `dual_frame_large_sieve_one`: for `Q = 1` one has `c_W = 1` (for
  nonempty `W`), the bound is `∑_{z∈W} |y z|² ≤ ∑_z |y z|²`, and the corollary is the trivial bound "a
  restriction of the full large sieve is a large sieve".

The factorization behind it is `A = P_W Q^{-1/2}`, `Y = Q^{1/2} M`: a reformulation of RIP, exact as
`Q → P_W`, and useful only through the choice of `Q`. Real parts are taken because `⟨y, Q y⟩` is real for a
Hermitian `Q`.
-/

set_option autoImplicit false

namespace QRH.ArviKWall

open Finset Matrix
open scoped BigOperators ComplexOrder ComplexConjugate Matrix

section DualFrame

variable {ρ : Type*} [Fintype ρ]

/-- Hermitian symmetry of the `Q`-form: `conj ⟨x, Q y⟩ = ⟨y, Q x⟩`. -/
theorem qform_conj_symm {Q : Matrix ρ ρ ℂ} (hQ : Q.IsHermitian) (x y : ρ → ℂ) :
    star (star x ⬝ᵥ (Q *ᵥ y)) = star y ⬝ᵥ (Q *ᵥ x) := by
  rw [star_dotProduct x (Q *ᵥ y), star_star, star_mulVec, hQ.eq, dotProduct_mulVec]

/-- **Cauchy–Schwarz for a positive semidefinite form:** `|⟨u, Q w⟩|² ≤ Re⟨u, Q u⟩ · Re⟨w, Q w⟩`. -/
theorem qform_cauchy_schwarz {Q : Matrix ρ ρ ℂ} (hQ : Q.PosSemidef) (u w : ρ → ℂ) :
    ‖star u ⬝ᵥ (Q *ᵥ w)‖ ^ 2 ≤ (star u ⬝ᵥ (Q *ᵥ u)).re * (star w ⬝ᵥ (Q *ᵥ w)).re := by
  let c : PreInnerProductSpace.Core ℂ (ρ → ℂ) :=
    { inner := fun u w => star u ⬝ᵥ (Q *ᵥ w)
      conj_inner_symm := fun x y => by simpa using qform_conj_symm hQ.isHermitian y x
      re_inner_nonneg := fun x => by simpa using hQ.re_dotProduct_nonneg x
      add_left := fun x y z => by simp [star_add, add_dotProduct]
      smul_left := fun x y r => by simp [star_smul, smul_dotProduct] }
  have h : ‖star u ⬝ᵥ (Q *ᵥ w)‖ * ‖star w ⬝ᵥ (Q *ᵥ u)‖ ≤
      (star u ⬝ᵥ (Q *ᵥ u)).re * (star w ⬝ᵥ (Q *ᵥ w)).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (F := ρ → ℂ) u w
  have hsym : ‖star w ⬝ᵥ (Q *ᵥ u)‖ = ‖star u ⬝ᵥ (Q *ᵥ w)‖ := by
    rw [← qform_conj_symm hQ.isHermitian u w, norm_star]
  rw [hsym] at h
  rwa [sq]

/-- A crude bound on the form of a vector with all coordinates of modulus at most `1`. -/
theorem form_re_le {A : Matrix ρ ρ ℂ} {v : ρ → ℂ} (hv : ∀ z, ‖v z‖ ≤ 1) :
    (star v ⬝ᵥ (A *ᵥ v)).re ≤ ∑ z, ∑ z', ‖A z z'‖ := by
  refine (Complex.re_le_norm _).trans ?_
  have hsum : star v ⬝ᵥ (A *ᵥ v) = ∑ z, ∑ z', star (v z) * (A z z' * v z') := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z' _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have h3 : 0 ≤ ‖A z z'‖ := norm_nonneg _
  calc ‖v z‖ * (‖A z z'‖ * ‖v z'‖) ≤ 1 * (‖A z z'‖ * 1) :=
        mul_le_mul (hv z) (mul_le_mul_of_nonneg_left (hv z') h3) (by positivity) zero_le_one
    _ = ‖A z z'‖ := by ring

/-- A unit vector has all coordinates of modulus at most `1`. -/
theorem norm_le_one_of_sum_sq {v : ρ → ℂ} (hv : ∑ z, ‖v z‖ ^ 2 = 1) (z : ρ) : ‖v z‖ ≤ 1 := by
  have h : ‖v z‖ ^ 2 ≤ 1 := by
    rw [← hv]
    exact Finset.single_le_sum (f := fun z => ‖v z‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ z)
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

variable [DecidableEq ρ]

/-- **Dual Cauchy–Schwarz.** If `Q ⪰ 0` and `Q P = 1`, then `|⟨v, y⟩|² ≤ Re⟨v, P v⟩ · Re⟨y, Q y⟩`.
(With `P = Q⁻¹` this is `|⟨v, y⟩|² ≤ ⟨v, Q⁻¹ v⟩ ⟨y, Q y⟩`.) -/
theorem dual_cauchy_schwarz {Q P : Matrix ρ ρ ℂ} (hQ : Q.PosSemidef) (hQP : Q * P = 1)
    (v y : ρ → ℂ) :
    ‖star v ⬝ᵥ y‖ ^ 2 ≤ (star v ⬝ᵥ (P *ᵥ v)).re * (star y ⬝ᵥ (Q *ᵥ y)).re := by
  have hQx : Q *ᵥ (P *ᵥ v) = v := by rw [mulVec_mulVec, hQP, one_mulVec]
  have h1 : star v ⬝ᵥ y = star (P *ᵥ v) ⬝ᵥ (Q *ᵥ y) := by
    conv_lhs => rw [← hQx, star_mulVec, hQ.isHermitian.eq, ← dotProduct_mulVec]
  have h2 : (star (P *ᵥ v) ⬝ᵥ (Q *ᵥ (P *ᵥ v))).re = (star v ⬝ᵥ (P *ᵥ v)).re := by
    rw [hQx, star_dotProduct (P *ᵥ v) v, Complex.star_def, Complex.conj_re]
  have h := qform_cauchy_schwarz hQ (P *ᵥ v) y
  rw [h2, ← h1] at h
  exact h

/-- `c_W(Q)`: the supremum of `Re⟨v, Q⁻¹ v⟩` over unit vectors `v` supported on the row subset `W`. -/
noncomputable def cW (Q : Matrix ρ ρ ℂ) (W : Finset ρ) : ℝ :=
  sSup {t : ℝ | ∃ v : ρ → ℂ, (∀ z, z ∉ W → v z = 0) ∧ ∑ z, ‖v z‖ ^ 2 = 1 ∧
    t = (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re}

theorem cW_bddAbove (Q : Matrix ρ ρ ℂ) (W : Finset ρ) :
    BddAbove {t : ℝ | ∃ v : ρ → ℂ, (∀ z, z ∉ W → v z = 0) ∧ ∑ z, ‖v z‖ ^ 2 = 1 ∧
      t = (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re} := by
  refine ⟨∑ z, ∑ z', ‖Q⁻¹ z z'‖, ?_⟩
  rintro t ⟨v, -, hv1, rfl⟩
  exact form_re_le (norm_le_one_of_sum_sq hv1)

/-- Every unit vector supported on `W` is below the supremum. -/
theorem form_le_cW {Q : Matrix ρ ρ ℂ} (W : Finset ρ) {v : ρ → ℂ} (hv : ∀ z, z ∉ W → v z = 0)
    (hv1 : ∑ z, ‖v z‖ ^ 2 = 1) : (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re ≤ cW Q W :=
  le_csSup (cW_bddAbove Q W) ⟨v, hv, hv1, rfl⟩

theorem cW_nonneg {Q : Matrix ρ ρ ℂ} (hQ : Q.PosDef) (W : Finset ρ) : 0 ≤ cW Q W := by
  refine Real.sSup_nonneg ?_
  rintro t ⟨v, -, -, rfl⟩
  simpa using hQ.inv.posSemidef.re_dotProduct_nonneg v

/-- The defining inequality of `c_W`, for vectors of any length supported on `W`:
`Re⟨v, Q⁻¹ v⟩ ≤ c_W(Q) · ‖v‖²`. -/
theorem form_le_cW_mul {Q : Matrix ρ ρ ℂ} (W : Finset ρ) {v : ρ → ℂ} (hv : ∀ z, z ∉ W → v z = 0) :
    (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re ≤ cW Q W * ∑ z, ‖v z‖ ^ 2 := by
  by_cases hN : ∑ z, ‖v z‖ ^ 2 = 0
  · have hv0 : v = 0 := by
      funext z
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg ‖v z‖)).mp hN z (mem_univ z)
      simpa using this
    subst hv0
    simp
  · have hNpos : 0 < ∑ z, ‖v z‖ ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hN)
    generalize hNdef : ∑ z, ‖v z‖ ^ 2 = N at hNpos ⊢
    have hs2 : ((Real.sqrt N)⁻¹) ^ 2 * N = 1 := by
      rw [inv_pow, Real.sq_sqrt hNpos.le]; field_simp
    generalize hs : (Real.sqrt N)⁻¹ = s at hs2
    have hsupp : ∀ z, z ∉ W → ((s : ℂ) • v) z = 0 := by
      intro z hz; simp [hv z hz]
    have hnorm : ∑ z, ‖((s : ℂ) • v) z‖ ^ 2 = 1 := by
      have : ∀ z, ‖((s : ℂ) • v) z‖ ^ 2 = s ^ 2 * ‖v z‖ ^ 2 := by
        intro z
        simp [mul_pow]
      simp_rw [this, ← Finset.mul_sum, hNdef]
      exact hs2
    have hform : (star ((s : ℂ) • v) ⬝ᵥ (Q⁻¹ *ᵥ ((s : ℂ) • v))).re =
        s ^ 2 * (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re := by
      have : star ((s : ℂ) • v) ⬝ᵥ (Q⁻¹ *ᵥ ((s : ℂ) • v)) =
          ((s ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ (Q⁻¹ *ᵥ v)) := by
        simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
        ring
      rw [this, Complex.re_ofReal_mul]
    have h := form_le_cW (Q := Q) W hsupp hnorm
    rw [hform] at h
    calc (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re = (s ^ 2 * (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re) * N := by
          have : (s ^ 2 * (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re) * N =
              (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re * (s ^ 2 * N) := by ring
          rw [this, hs2, mul_one]
      _ ≤ cW Q W * N := mul_le_mul_of_nonneg_right h hNpos.le

/-- `|⟨v, y⟩|² ≤ ⟨v, Q⁻¹ v⟩ ⟨y, Q y⟩` for a positive definite `Q`. -/
theorem dual_cauchy_schwarz_inv {Q : Matrix ρ ρ ℂ} (hQ : Q.PosDef) (v y : ρ → ℂ) :
    ‖star v ⬝ᵥ y‖ ^ 2 ≤ (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re * (star y ⬝ᵥ (Q *ᵥ y)).re :=
  dual_cauchy_schwarz hQ.posSemidef
    (Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit)) v y

/-- **The dual-frame bound, for any constant `c ≥ 0` that bounds the dual form on `W`**, i.e.
`Re⟨v, Q⁻¹ v⟩ ≤ c ‖v‖²` for every `v` supported on `W`. -/
theorem dual_frame_bound_of_le {Q : Matrix ρ ρ ℂ} (hQ : Q.PosDef) (W : Finset ρ) {c : ℝ}
    (hc0 : 0 ≤ c)
    (hc : ∀ v : ρ → ℂ, (∀ z, z ∉ W → v z = 0) →
      (star v ⬝ᵥ (Q⁻¹ *ᵥ v)).re ≤ c * ∑ z, ‖v z‖ ^ 2) (y : ρ → ℂ) :
    ∑ z ∈ W, ‖y z‖ ^ 2 ≤ c * (star y ⬝ᵥ (Q *ᵥ y)).re := by
  set S := ∑ z ∈ W, ‖y z‖ ^ 2 with hS
  set T := (star y ⬝ᵥ (Q *ᵥ y)).re with hT
  have hT0 : 0 ≤ T := by simpa [hT] using hQ.posSemidef.re_dotProduct_nonneg y
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the restriction `P_W y` of `y` to `W`
  let v : ρ → ℂ := fun z => if z ∈ W then y z else 0
  have hvsupp : ∀ z, z ∉ W → v z = 0 := fun z hz => by simp [v, hz]
  have hvsum : ∑ z, ‖v z‖ ^ 2 = S := by
    have : ∀ z, ‖v z‖ ^ 2 = if z ∈ W then ‖y z‖ ^ 2 else 0 := by
      intro z
      by_cases hz : z ∈ W <;> simp [v, hz]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hvy : star v ⬝ᵥ y = (S : ℂ) := by
    have : ∀ z, star (v z) * y z = if z ∈ W then ((‖y z‖ ^ 2 : ℝ) : ℂ) else 0 := by
      intro z
      by_cases hz : z ∈ W
      · simp [v, hz, Complex.conj_mul']
      · simp [v, hz]
    have h2 : star v ⬝ᵥ y = ∑ z, star (v z) * y z := rfl
    rw [h2]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, hS]
    push_cast
    rfl
  have hcs := dual_cauchy_schwarz_inv hQ v y
  rw [hvy, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] at hcs
  have hform := hc v hvsupp
  rw [hvsum] at hform
  by_cases hS' : S = 0
  · rw [hS']; exact mul_nonneg hc0 hT0
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS')
    have h2 : S * S ≤ S * (c * T) :=
      calc S * S = S ^ 2 := (sq S).symm
        _ ≤ (c * S) * T := hcs.trans (mul_le_mul_of_nonneg_right hform hT0)
        _ = S * (c * T) := by ring
    exact le_of_mul_le_mul_left h2 hSpos

/-- **The dual-frame (Q-metric) bound.** For a positive definite Hermitian `Q` on the row space, a row
subset `W` and a row vector `y`:
`∑_{z∈W} |y z|² ≤ c_W(Q) · ⟨y, Q y⟩`, where `c_W(Q)` is the supremum of `⟨v, Q⁻¹ v⟩` over unit vectors
`v` supported on `W`. -/
theorem dual_frame_bound {Q : Matrix ρ ρ ℂ} (hQ : Q.PosDef) (W : Finset ρ) (y : ρ → ℂ) :
    ∑ z ∈ W, ‖y z‖ ^ 2 ≤ cW Q W * (star y ⬝ᵥ (Q *ᵥ y)).re :=
  dual_frame_bound_of_le hQ W (cW_nonneg hQ W) (fun _ hv => form_le_cW_mul W hv) y

/-- **The corollary for `y = M a`.** Sources are indexed by a finite type `σ` and `M` is a matrix with
rows `ρ`. If `⟨M a, Q M a⟩ ≤ λ ‖a‖²` for all `a`, then on every row subset `W`
`∑_{z∈W} |(M a) z|² ≤ c_W(Q) · λ · ‖a‖²`. -/
theorem dual_frame_large_sieve {σ : Type*} [Fintype σ] {Q : Matrix ρ ρ ℂ} (hQ : Q.PosDef)
    (M : Matrix ρ σ ℂ) (W : Finset ρ) {lam : ℝ}
    (hlam : ∀ a : σ → ℂ, (star (M *ᵥ a) ⬝ᵥ (Q *ᵥ (M *ᵥ a))).re ≤ lam * ∑ n, ‖a n‖ ^ 2)
    (a : σ → ℂ) :
    ∑ z ∈ W, ‖(M *ᵥ a) z‖ ^ 2 ≤ cW Q W * lam * ∑ n, ‖a n‖ ^ 2 :=
  calc ∑ z ∈ W, ‖(M *ᵥ a) z‖ ^ 2 ≤ cW Q W * (star (M *ᵥ a) ⬝ᵥ (Q *ᵥ (M *ᵥ a))).re :=
        dual_frame_bound hQ W (M *ᵥ a)
    _ ≤ cW Q W * (lam * ∑ n, ‖a n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hlam a) (cW_nonneg hQ W)
    _ = cW Q W * lam * ∑ n, ‖a n‖ ^ 2 := by ring

/-! ### `Q = 1` recovers the trivial bound -/

/-- For `Q = 1` the form `⟨y, Q y⟩` is the squared norm. -/
theorem re_form_one (y : ρ → ℂ) :
    (star y ⬝ᵥ ((1 : Matrix ρ ρ ℂ) *ᵥ y)).re = ∑ z, ‖y z‖ ^ 2 := by
  have h : star y ⬝ᵥ ((1 : Matrix ρ ρ ℂ) *ᵥ y) = ∑ z, star (y z) * y z := by
    rw [one_mulVec]; rfl
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- With `Q = 1` the constant `c_W` is at most `1`. -/
theorem cW_one_le (W : Finset ρ) : cW (1 : Matrix ρ ρ ℂ) W ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro t ⟨v, -, hv1, rfl⟩
  rw [inv_one, re_form_one, hv1]

/-- With `Q = 1` and `W` nonempty the constant `c_W` is exactly `1`. -/
theorem cW_one_eq {W : Finset ρ} (hW : W.Nonempty) : cW (1 : Matrix ρ ρ ℂ) W = 1 := by
  refine le_antisymm (cW_one_le W) ?_
  obtain ⟨z₀, hz₀⟩ := hW
  have hsupp : ∀ z, z ∉ W → (Pi.single z₀ (1 : ℂ) : ρ → ℂ) z = 0 := by
    intro z hz
    have : z ≠ z₀ := fun h => hz (h ▸ hz₀)
    simp [this]
  have hsum : ∑ z, ‖(Pi.single z₀ (1 : ℂ) : ρ → ℂ) z‖ ^ 2 = 1 := by
    have : ∀ z, ‖(Pi.single z₀ (1 : ℂ) : ρ → ℂ) z‖ ^ 2 = if z = z₀ then 1 else 0 := by
      intro z
      by_cases h : z = z₀ <;> simp [h]
    simp [this]
  have := form_le_cW (Q := (1 : Matrix ρ ρ ℂ)) W hsupp hsum
  rwa [inv_one, re_form_one, hsum] at this

/-- **`Q = 1` recovers the trivial bound, pointwise.** For `Q = 1` and nonempty `W` the dual-frame bound
reads `∑_{z∈W} |y z|² ≤ ∑_z |y z|²`: restricting a sum of squares. -/
theorem dual_frame_bound_one {W : Finset ρ} (hW : W.Nonempty) (y : ρ → ℂ) :
    ∑ z ∈ W, ‖y z‖ ^ 2 ≤ ∑ z, ‖y z‖ ^ 2 := by
  have h := dual_frame_bound (Q := (1 : Matrix ρ ρ ℂ)) Matrix.PosDef.one W y
  rwa [cW_one_eq hW, one_mul, re_form_one] at h

/-- **`Q = 1` recovers the trivial bound.** With the identity metric the corollary says only that a
restriction of the full large sieve is a large sieve: `c_W(1) = 1` for every nonempty `W`. -/
theorem dual_frame_large_sieve_one {σ : Type*} [Fintype σ] (M : Matrix ρ σ ℂ) {W : Finset ρ}
    (hW : W.Nonempty) {lam : ℝ}
    (hlam : ∀ a : σ → ℂ, ∑ z, ‖(M *ᵥ a) z‖ ^ 2 ≤ lam * ∑ n, ‖a n‖ ^ 2) (a : σ → ℂ) :
    ∑ z ∈ W, ‖(M *ᵥ a) z‖ ^ 2 ≤ lam * ∑ n, ‖a n‖ ^ 2 := by
  have h := dual_frame_large_sieve (Q := (1 : Matrix ρ ρ ℂ)) Matrix.PosDef.one M W
    (lam := lam) (fun a => by rw [re_form_one]; exact hlam a) a
  rwa [cW_one_eq hW, one_mul] at h

end DualFrame

end QRH.ArviKWall

#print axioms QRH.ArviKWall.dual_cauchy_schwarz_inv
#print axioms QRH.ArviKWall.dual_frame_bound
#print axioms QRH.ArviKWall.dual_frame_large_sieve
#print axioms QRH.ArviKWall.dual_frame_bound_one
#print axioms QRH.ArviKWall.dual_frame_large_sieve_one
