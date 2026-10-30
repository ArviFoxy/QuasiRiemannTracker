import Submissions.arvi_rip.Coherence

/-!
# The centered fourth moment certifies RIP beyond the square-root barrier

Research file (QRH, RIP program (4); the fresh look's certificate (M₄)).

Let `O` be the off-diagonal Gram of columns `u_z` on a support `S`, `O z z' = ⟪u_z, u_{z'}⟫` for
`z ≠ z'`. Its square has entries `(O²)(z₁, z₃) = ∑_{z₂ ∈ S, z₂ ≠ z₁, z₃} ⟪u_{z₁}, u_{z₂}⟫⟪u_{z₂}, u_{z₃}⟫`
(the two-step, non-backtracking correlations). Then (`fourth_moment_rip`)

  `|‖∑ c_z u_z‖² − ∑ |c_z|² ‖u_z‖²| ≤ ‖O²‖_F^{1/2} ∑ |c_z|²`,

with `‖O²‖_F² = ∑_{z₁, z₃} |(O²)(z₁, z₃)|²`, which is the trace of the fourth power of `O`.

At the random-matrix scale, `‖O²‖_F² ≈ 2|S|³/n²` for `n`-dimensional unit columns, so the constant is
`(2|S|³/n²)^{1/4}`. That is `< 1` for `|S| ≲ n^{2/3}`, beyond the `√n` reach of coherence
(`coherence_order_barrier`). In the K-wall, `|W| = B^{1−δ}`, so the whole barrier range `1/3 ≤ δ < 1/2` is
covered, provided the sextic 4-cycles on `W` cancel at that scale.
-/

namespace QRH.ArviRIP

open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [DecidableEq ι]

/-- The off-diagonal Gram on `S`. -/
noncomputable def offG (u : ι → E) (z z' : ι) : ℂ := if z = z' then 0 else ⟪u z, u z'⟫_ℂ

/-- Its square restricted to `S`: two-step non-backtracking correlations. -/
noncomputable def offG2 (S : Finset ι) (u : ι → E) (z₁ z₃ : ι) : ℂ := ∑ z₂ ∈ S, offG u z₁ z₂ * offG u z₂ z₃

theorem offG_conj (u : ι → E) (z z' : ι) : conj (offG u z z') = offG u z' z := by
  unfold offG
  by_cases h : z = z'
  · subst h; simp
  · simp [h, Ne.symm h, inner_conj_symm]

omit [DecidableEq ι] in
/-- Cauchy–Schwarz for finite sums of complex numbers. -/
theorem norm_sum_mul_le_sqrt (S : Finset ι) (f g : ι → ℂ) :
    ‖∑ z ∈ S, f z * g z‖ ≤ Real.sqrt (∑ z ∈ S, ‖f z‖ ^ 2) * Real.sqrt (∑ z ∈ S, ‖g z‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∑ z ∈ S, ‖f z * g z‖ = ∑ z ∈ S, ‖f z‖ * ‖g z‖ :=
    Finset.sum_congr rfl fun z _ => norm_mul _ _
  rw [this]
  exact Real.sum_mul_le_sqrt_mul_sqrt S (fun z => ‖f z‖) (fun z => ‖g z‖)

/-- The quadratic form of `O`: `∑ conj(c_z) c_{z'} O(z, z')`. -/
noncomputable def formO (S : Finset ι) (u : ι → E) (c : ι → ℂ) : ℂ :=
  ∑ z ∈ S, ∑ z' ∈ S, conj (c z) * c z' * offG u z z'

/-- Gram expansion with the diagonal split off. -/
theorem norm_sq_split (S : Finset ι) (c : ι → ℂ) (u : ι → E) :
    ‖∑ z ∈ S, c z • u z‖ ^ 2 = ∑ z ∈ S, ‖c z‖ ^ 2 * ‖u z‖ ^ 2 + (formO S u c).re := by
  rw [norm_sq_eq_re, inner_sum_sum]
  have h : ∀ z ∈ S, ∑ z' ∈ S, conj (c z) * c z' * ⟪u z, u z'⟫_ℂ =
      ((‖c z‖ ^ 2 * ‖u z‖ ^ 2 : ℝ) : ℂ) + ∑ z' ∈ S, conj (c z) * c z' * offG u z z' := by
    intro z hz
    rw [← Finset.add_sum_erase S _ hz, ← Finset.add_sum_erase S (fun z' => conj (c z) * c z' * offG u z z') hz]
    have h1 : ⟪u z, u z⟫_ℂ = ((‖u z‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h2 : offG u z z = 0 := by simp [offG]
    have h3 : ∀ z' ∈ S.erase z, conj (c z) * c z' * ⟪u z, u z'⟫_ℂ = conj (c z) * c z' * offG u z z' := by
      intro z' hz'
      have hne : z ≠ z' := Ne.symm (Finset.ne_of_mem_erase hz')
      simp [offG, hne]
    rw [Finset.sum_congr rfl h3, h1, h2, Complex.conj_mul']
    push_cast; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Complex.add_re, ← Complex.ofReal_sum,
    Complex.ofReal_re]
  rfl

/-- `‖O c‖²` is the form of `O²`. -/
theorem normsq_Oc (S : Finset ι) (u : ι → E) (c : ι → ℂ) :
    ∑ z ∈ S, ‖∑ z' ∈ S, offG u z z' * c z'‖ ^ 2 =
      (∑ z' ∈ S, ∑ z'' ∈ S, conj (c z') * c z'' * offG2 S u z' z'').re := by
  have hsq : ∀ v : ℂ, ‖v‖ ^ 2 = (conj v * v).re := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have key : ∑ z ∈ S, conj (∑ z' ∈ S, offG u z z' * c z') * (∑ z'' ∈ S, offG u z z'' * c z'') =
      ∑ z' ∈ S, ∑ z'' ∈ S, conj (c z') * c z'' * offG2 S u z' z'' := by
    calc ∑ z ∈ S, conj (∑ z' ∈ S, offG u z z' * c z') * (∑ z'' ∈ S, offG u z z'' * c z'')
        = ∑ z ∈ S, ∑ z' ∈ S, ∑ z'' ∈ S, conj (offG u z z' * c z') * (offG u z z'' * c z'') := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [map_sum, Finset.sum_mul_sum]
      _ = ∑ z' ∈ S, ∑ z'' ∈ S, ∑ z ∈ S, conj (offG u z z' * c z') * (offG u z z'' * c z'') := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z' _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ z' ∈ S, ∑ z'' ∈ S, conj (c z') * c z'' * offG2 S u z' z'' := by
          refine Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun z'' _ => ?_
          rw [offG2, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [map_mul, offG_conj]
          ring
  simp_rw [hsq]
  rw [← Complex.re_sum, key]

/-- **Fourth-moment certificate.** -/
theorem fourth_moment_rip (S : Finset ι) (c : ι → ℂ) (u : ι → E) :
    |‖∑ z ∈ S, c z • u z‖ ^ 2 - ∑ z ∈ S, ‖c z‖ ^ 2 * ‖u z‖ ^ 2| ≤
      Real.sqrt (Real.sqrt (∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S u z₁ z₃‖ ^ 2)) * ∑ z ∈ S, ‖c z‖ ^ 2 := by
  set N2 := ∑ z ∈ S, ‖c z‖ ^ 2 with hN2
  set F := ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S u z₁ z₃‖ ^ 2 with hF
  have hN0 : 0 ≤ N2 := Finset.sum_nonneg fun z _ => by positivity
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  -- |form O| ≤ ‖c‖ ‖Oc‖
  set Oc := fun z => ∑ z' ∈ S, offG u z z' * c z' with hOc
  have h1 : ‖formO S u c‖ ≤ Real.sqrt N2 * Real.sqrt (∑ z ∈ S, ‖Oc z‖ ^ 2) := by
    have : formO S u c = ∑ z ∈ S, conj (c z) * Oc z := by
      simp only [formO, hOc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => by ring
    rw [this]
    refine (norm_sum_mul_le_sqrt S (fun z => conj (c z)) Oc).trans (le_of_eq ?_)
    simp [hN2]
  -- ‖Oc‖² = form of O² ≤ ‖c‖ ‖O² c‖ ≤ ‖c‖² ‖O²‖_F
  have h2 : ∑ z ∈ S, ‖Oc z‖ ^ 2 ≤ N2 * Real.sqrt F := by
    rw [hOc, normsq_Oc]
    refine (Complex.re_le_norm _).trans ?_
    have hrow : ∀ z' ∈ S, ‖∑ z'' ∈ S, conj (c z') * c z'' * offG2 S u z' z''‖ ≤
        ‖c z'‖ * (Real.sqrt N2 * Real.sqrt (∑ z'' ∈ S, ‖offG2 S u z' z''‖ ^ 2)) := by
      intro z' _
      have e : ∑ z'' ∈ S, conj (c z') * c z'' * offG2 S u z' z'' =
          conj (c z') * ∑ z'' ∈ S, c z'' * offG2 S u z' z'' := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z'' _ => by ring
      rw [e, norm_mul, Complex.norm_conj]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact norm_sum_mul_le_sqrt S c (fun z'' => offG2 S u z' z'')
    calc ‖∑ z' ∈ S, ∑ z'' ∈ S, conj (c z') * c z'' * offG2 S u z' z''‖
        ≤ ∑ z' ∈ S, ‖c z'‖ * (Real.sqrt N2 * Real.sqrt (∑ z'' ∈ S, ‖offG2 S u z' z''‖ ^ 2)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hrow)
      _ = Real.sqrt N2 * ∑ z' ∈ S, ‖c z'‖ * Real.sqrt (∑ z'' ∈ S, ‖offG2 S u z' z''‖ ^ 2) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z' _ => by ring
      _ ≤ Real.sqrt N2 * (Real.sqrt N2 * Real.sqrt F) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          have := Real.sum_mul_le_sqrt_mul_sqrt S (fun z' => ‖c z'‖)
            (fun z' => Real.sqrt (∑ z'' ∈ S, ‖offG2 S u z' z''‖ ^ 2))
          refine this.trans (le_of_eq ?_)
          congr 2
          all_goals first
            | rfl
            | exact Finset.sum_congr rfl fun z' _ =>
                Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
      _ = N2 * Real.sqrt F := by
          rw [← mul_assoc, Real.mul_self_sqrt hN0]
  have h3 : ‖formO S u c‖ ≤ Real.sqrt (Real.sqrt F) * N2 := by
    refine h1.trans ?_
    have hs : Real.sqrt (∑ z ∈ S, ‖Oc z‖ ^ 2) ≤ Real.sqrt (N2 * Real.sqrt F) := Real.sqrt_le_sqrt h2
    calc Real.sqrt N2 * Real.sqrt (∑ z ∈ S, ‖Oc z‖ ^ 2)
        ≤ Real.sqrt N2 * Real.sqrt (N2 * Real.sqrt F) :=
          mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = Real.sqrt (Real.sqrt F) * N2 := by
          rw [Real.sqrt_mul hN0, ← mul_assoc, Real.mul_self_sqrt hN0]; ring
  rw [norm_sq_split]
  have : ∑ z ∈ S, ‖c z‖ ^ 2 * ‖u z‖ ^ 2 + (formO S u c).re - ∑ z ∈ S, ‖c z‖ ^ 2 * ‖u z‖ ^ 2 =
      (formO S u c).re := by ring
  rw [this]
  exact (Complex.abs_re_le_norm _).trans h3

end QRH.ArviRIP

#print axioms QRH.ArviRIP.fourth_moment_rip
