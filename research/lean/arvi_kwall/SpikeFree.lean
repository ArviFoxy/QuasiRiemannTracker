import Mathlib

/-!
# The large sieve with the spikes removed

Research file (QRH, K-wall; the journal entries "Where the theta excess lives" and "large sieve off V").

Sources are indexed by a finite type `σ`, rows by a finite type `ρ`, and `M : Matrix ρ σ ℂ` acts by
`(M a) z = ∑_n M z n * a n`. Write `⟨f, a⟩ = ∑_n conj (f n) * a n` (Lean: `star f ⬝ᵥ a`).

A **corrected large sieve** (`CorrectedLargeSieve M Δ f w`) with spike directions `f k` and weights `w k`
(`k` in a finite type `κ`) is

  `∑_z |(M a) z|² ≤ Δ ‖a‖² + ∑_k w_k |⟨f_k, a⟩|²`   for every `a`.

Here `Δ` is the diagonal-size constant and the second term carries the spikes (the theta excess). Then:

* `selected_of_corrected`: on every row subset `W`, `∑_{z∈W} |(M a) z|² ≤ Δ ‖a‖² + ∑_k w_k |⟨f_k, a⟩|²`
  (restricting a sum of squares can only decrease it).
* `off_spikes`: if `⟨f_k, a⟩ = 0` for all `k`, then `∑_z |(M a) z|² ≤ Δ ‖a‖²`.
* `detector_condition`: if `∑_k w_k |⟨f_k, a⟩|² ≤ η ‖a‖²` (the detector condition), then
  `∑_{z∈W} |(M a) z|² ≤ (Δ + η) ‖a‖²` for every `W`. No thin-set argument is needed.
* `exists_unit_orth_large` and `exists_unit_orth_form`: dimension counting. If a form is `≥ Δ' ‖x‖²` on a
  subspace `E` of dimension `k + 1`, every subspace `V` of dimension `≤ k` has a unit vector `x ∈ E`
  orthogonal to `V` with form value `≥ Δ'` (since `E ∩ Vᗮ ≠ 0`).
* `detectorSpan_finrank_ge` and `card_detectors_ge`: so the spikes must be high-dimensional. If `M` has the
  corrected large sieve with constant `Δ` and `‖M a‖² ≥ Δ' ‖a‖²` on a subspace of dimension `k + 1` with
  `Δ' > Δ`, then the span of the `f_k` has dimension at least `k + 1`, and there are at least `k + 1`
  detector vectors. With each twisted theta carrying its own excess, `V` cannot be low-dimensional.

The weights `w k` may be any reals in the proofs below; in the application they are nonnegative.
-/

set_option autoImplicit false

namespace QRH.ArviKWall

open Finset Matrix Module
open scoped BigOperators ComplexConjugate Matrix

section SpikeFree

variable {ρ σ κ : Type*} [Fintype ρ] [Fintype σ] [Fintype κ]

/-- **A large sieve with the spikes corrected.** For every `a`,
`∑_z |(M a) z|² ≤ Δ ‖a‖² + ∑_k w_k |⟨f_k, a⟩|²`, with `⟨f, a⟩ = ∑_n conj (f n) * a n`. -/
def CorrectedLargeSieve (M : Matrix ρ σ ℂ) (Δ : ℝ) (f : κ → σ → ℂ) (w : κ → ℝ) : Prop :=
  ∀ a : σ → ℂ, ∑ z, ‖(M *ᵥ a) z‖ ^ 2 ≤ Δ * ∑ n, ‖a n‖ ^ 2 + ∑ k, w k * ‖star (f k) ⬝ᵥ a‖ ^ 2

/-- **(i)** The corrected bound holds on every row subset: restriction can only decrease a sum of
squares. -/
theorem selected_of_corrected {M : Matrix ρ σ ℂ} {Δ : ℝ} {f : κ → σ → ℂ} {w : κ → ℝ}
    (h : CorrectedLargeSieve M Δ f w) (W : Finset ρ) (a : σ → ℂ) :
    ∑ z ∈ W, ‖(M *ᵥ a) z‖ ^ 2 ≤ Δ * ∑ n, ‖a n‖ ^ 2 + ∑ k, w k * ‖star (f k) ⬝ᵥ a‖ ^ 2 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W) (fun _ _ _ => sq_nonneg _)).trans
    (h a)

/-- **(ii)** Off the spikes the bound is the diagonal one: if `⟨f_k, a⟩ = 0` for all `k`, then
`∑_z |(M a) z|² ≤ Δ ‖a‖²`. -/
theorem off_spikes {M : Matrix ρ σ ℂ} {Δ : ℝ} {f : κ → σ → ℂ} {w : κ → ℝ}
    (h : CorrectedLargeSieve M Δ f w) (a : σ → ℂ) (ha : ∀ k, star (f k) ⬝ᵥ a = 0) :
    ∑ z, ‖(M *ᵥ a) z‖ ^ 2 ≤ Δ * ∑ n, ‖a n‖ ^ 2 := by
  have := h a
  simpa [ha] using this

/-- **(iii)** The detector condition. If the spike term of `a` is at most `η ‖a‖²`, then on every row
subset `W`, `∑_{z∈W} |(M a) z|² ≤ (Δ + η) ‖a‖²`. -/
theorem detector_condition {M : Matrix ρ σ ℂ} {Δ : ℝ} {f : κ → σ → ℂ} {w : κ → ℝ}
    (h : CorrectedLargeSieve M Δ f w) (a : σ → ℂ) {η : ℝ}
    (hη : ∑ k, w k * ‖star (f k) ⬝ᵥ a‖ ^ 2 ≤ η * ∑ n, ‖a n‖ ^ 2) (W : Finset ρ) :
    ∑ z ∈ W, ‖(M *ᵥ a) z‖ ^ 2 ≤ (Δ + η) * ∑ n, ‖a n‖ ^ 2 := by
  have := selected_of_corrected h W a
  linarith only [this, hη]

/-- The detector condition for all vectors turns the corrected sieve into a plain large sieve with
constant `Δ + η` on every row subset. -/
theorem plain_of_detector_bound {M : Matrix ρ σ ℂ} {Δ : ℝ} {f : κ → σ → ℂ} {w : κ → ℝ}
    (h : CorrectedLargeSieve M Δ f w) {η : ℝ}
    (hη : ∀ a : σ → ℂ, ∑ k, w k * ‖star (f k) ⬝ᵥ a‖ ^ 2 ≤ η * ∑ n, ‖a n‖ ^ 2) (W : Finset ρ)
    (a : σ → ℂ) : ∑ z ∈ W, ‖(M *ᵥ a) z‖ ^ 2 ≤ (Δ + η) * ∑ n, ‖a n‖ ^ 2 :=
  detector_condition h a (hη a) W

section Dimension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- Dimension counting: `E ∩ Vᗮ ≠ 0` when `dim E = k + 1` and `dim V ≤ k`, so it contains a unit vector. -/
theorem exists_unit_mem_orth (E V : Submodule ℂ H) {k : ℕ} (hE : finrank ℂ E = k + 1)
    (hV : finrank ℂ V ≤ k) : ∃ x : H, x ∈ E ∧ x ∈ Vᗮ ∧ ‖x‖ = 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq E Vᗮ
  have h2 := Submodule.finrank_add_finrank_orthogonal V
  have h3 : finrank ℂ ↥(E ⊔ Vᗮ) ≤ finrank ℂ H := Submodule.finrank_le _
  have hpos : finrank ℂ ↥(E ⊓ Vᗮ) ≠ 0 := by omega
  have hne : E ⊓ Vᗮ ≠ ⊥ := fun h => hpos (by rw [h]; exact finrank_bot ℂ H)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨((‖x‖ : ℂ))⁻¹ • x, Submodule.smul_mem _ _ (Submodule.mem_inf.mp hx).1,
    Submodule.smul_mem _ _ (Submodule.mem_inf.mp hx).2, ?_⟩
  exact norm_smul_inv_norm (𝕜 := ℂ) hx0

/-- **(iv) A large form on `E` survives orthogonality to a smaller `V`.** If `q x ≥ Δ' ‖x‖²` on a subspace
`E` of dimension `k + 1` and `V` has dimension at most `k`, then some unit vector `x ∈ E` is orthogonal to
`V` and has `q x ≥ Δ'`. (For a positive semidefinite Hermitian form `A` take `q x = Re⟨x, A x⟩`.) -/
theorem exists_unit_orth_large (q : H → ℝ) {Δ' : ℝ} (E V : Submodule ℂ H) {k : ℕ}
    (hE : finrank ℂ E = k + 1) (hV : finrank ℂ V ≤ k) (hq : ∀ x ∈ E, Δ' * ‖x‖ ^ 2 ≤ q x) :
    ∃ x : H, x ∈ E ∧ x ∈ Vᗮ ∧ ‖x‖ = 1 ∧ Δ' ≤ q x := by
  obtain ⟨x, hxE, hxV, hx1⟩ := exists_unit_mem_orth E V hE hV
  refine ⟨x, hxE, hxV, hx1, ?_⟩
  have := hq x hxE
  rwa [hx1, one_pow, mul_one] at this

/-- The same for the form `x ↦ Re⟨x, A x⟩` of an operator `A`: if `A ≥ Δ'` on a subspace `E` of dimension
`k + 1`, every subspace `V` of dimension `≤ k` has a unit vector `x ⊥ V` in `E` with `Re⟨x, A x⟩ ≥ Δ'`. -/
theorem exists_unit_orth_form (A : H →ₗ[ℂ] H) {Δ' : ℝ} (E V : Submodule ℂ H) {k : ℕ}
    (hE : finrank ℂ E = k + 1) (hV : finrank ℂ V ≤ k)
    (hA : ∀ x ∈ E, Δ' * ‖x‖ ^ 2 ≤ (inner ℂ x (A x)).re) :
    ∃ x : H, x ∈ E ∧ x ∈ Vᗮ ∧ ‖x‖ = 1 ∧ Δ' ≤ (inner ℂ x (A x)).re :=
  exists_unit_orth_large (fun x => (inner ℂ x (A x)).re) E V hE hV hA

end Dimension

/-! ### The detector span must be high-dimensional -/

/-- The span of the detector vectors `f k`, inside `ℓ²(σ)`. -/
noncomputable def detectorSpan (f : κ → σ → ℂ) : Submodule ℂ (EuclideanSpace ℂ σ) :=
  Submodule.span ℂ (Set.range fun k => (WithLp.toLp 2 (f k) : EuclideanSpace ℂ σ))

omit [Fintype κ] in
/-- Orthogonality to the detector span is the vanishing of all the pairings `⟨f k, a⟩`. -/
theorem mem_detectorSpan_orthogonal {f : κ → σ → ℂ} {a : EuclideanSpace ℂ σ}
    (ha : a ∈ (detectorSpan f)ᗮ) (k : κ) : star (f k) ⬝ᵥ a.ofLp = 0 := by
  have h := (Submodule.mem_orthogonal _ _).mp ha (WithLp.toLp 2 (f k))
    (Submodule.subset_span ⟨k, rfl⟩)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  simpa using h

/-- **The detector span must be high-dimensional.** Suppose `M` satisfies the corrected large sieve with
constant `Δ` and detector vectors `f k`, and that `‖M a‖² ≥ Δ' ‖a‖²` on a subspace `E` of dimension
`k + 1`, with `Δ' > Δ`. Then the span of the `f k` has dimension at least `k + 1`. -/
theorem detectorSpan_finrank_ge {M : Matrix ρ σ ℂ} {Δ Δ' : ℝ} {f : κ → σ → ℂ} {w : κ → ℝ}
    (h : CorrectedLargeSieve M Δ f w) (hΔ : Δ < Δ') (E : Submodule ℂ (EuclideanSpace ℂ σ)) {k : ℕ}
    (hE : finrank ℂ E = k + 1)
    (hlow : ∀ a ∈ E, Δ' * ∑ n, ‖a.ofLp n‖ ^ 2 ≤ ∑ z, ‖(M *ᵥ a.ofLp) z‖ ^ 2) :
    k + 1 ≤ finrank ℂ (detectorSpan f) := by
  by_contra hcon
  have hV : finrank ℂ (detectorSpan f) ≤ k := by omega
  obtain ⟨x, hxE, hxV, hx1, hx⟩ := exists_unit_orth_large
    (fun a : EuclideanSpace ℂ σ => ∑ z, ‖(M *ᵥ a.ofLp) z‖ ^ 2) (Δ' := Δ') E (detectorSpan f) hE hV
    (fun a ha => by simpa [EuclideanSpace.norm_sq_eq] using hlow a ha)
  have hsum : ∑ n, ‖x.ofLp n‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hx1, one_pow]
  have hoff := off_spikes h x.ofLp (mem_detectorSpan_orthogonal hxV)
  rw [hsum, mul_one] at hoff
  linarith only [hoff, hx, hΔ]

/-- Counting form: at least `k + 1` detector vectors are needed. -/
theorem card_detectors_ge {M : Matrix ρ σ ℂ} {Δ Δ' : ℝ} {f : κ → σ → ℂ} {w : κ → ℝ}
    (h : CorrectedLargeSieve M Δ f w) (hΔ : Δ < Δ') (E : Submodule ℂ (EuclideanSpace ℂ σ)) {k : ℕ}
    (hE : finrank ℂ E = k + 1)
    (hlow : ∀ a ∈ E, Δ' * ∑ n, ‖a.ofLp n‖ ^ 2 ≤ ∑ z, ‖(M *ᵥ a.ofLp) z‖ ^ 2) :
    k + 1 ≤ Fintype.card κ :=
  (detectorSpan_finrank_ge h hΔ E hE hlow).trans
    (finrank_range_le_card (fun k => (WithLp.toLp 2 (f k) : EuclideanSpace ℂ σ)))

end SpikeFree

end QRH.ArviKWall

#print axioms QRH.ArviKWall.selected_of_corrected
#print axioms QRH.ArviKWall.off_spikes
#print axioms QRH.ArviKWall.detector_condition
#print axioms QRH.ArviKWall.exists_unit_orth_form
#print axioms QRH.ArviKWall.detectorSpan_finrank_ge
#print axioms QRH.ArviKWall.card_detectors_ge
