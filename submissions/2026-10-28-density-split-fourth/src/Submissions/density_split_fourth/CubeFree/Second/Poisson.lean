/- Copyright (c) 2026 Sil. Apache-2.0.
The second Poisson split and the two-sided Cauchy over labels (CF Sections 4-5).

After the selection of `D`, the D-Cauchy and the D⁴ transfer, the second Poisson step writes
the (first-divisor summed) side energy as
  zero frequency + fixed-inducing rows (`partRows true`) + nonfixed rows (`partRows false`)
  + tails.
`poisson_split` is the exact finite split of a dual sum by the two row predicates.
The nonfixed rows are grouped by second labels `x`; each label contributes the correlation
of the two physical columns of the second Gauss correlation, `∑_r A_x(r) conj B_x(r)`, with a
nonnegative scalar label weight. `two_sided_cauchy` bounds the weighted label sum by the
geometric mean of the two weighted one-sided label energies; each of these is then bounded by
Seam B (`GroupedSideBound`) in `Second/Side.lean`.

`SecondSplit` records the split of one side as data: it is the interface that the concrete
second-step forks (FP `MixedActual*`, `MixedPoissonCompletion`, `MixedPoissonLocalization`,
`MixedLocalizedDictionary`, OAI `SecondBlockAggregate`/`SecondRetainedAggregate`/
`SecondEnergySplit`) instantiate. The zero-frequency and fixed-inducing parts are bounded
separately (diagonals and the α < 2/3 principal ledger, WP-J). -/
import Submissions.density_split_fourth.CubeFree.Second.SeamBUse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Second
noncomputable section
open scoped BigOperators Classical

/-! ### The exact split -/

/-- Exact split of a dual sum into zero frequency, fixed-inducing and nonfixed rows. -/
theorem poisson_split {R M : Type*} [AddCommMonoid M] (rows : Finset R) (zero fixed : R → Prop)
    (f : R → M) :
    ∑ r ∈ rows, f r =
      ∑ r ∈ rows.filter zero, f r +
        (∑ r ∈ (rows.filter (fun r => ¬ zero r)).filter fixed, f r +
          ∑ r ∈ (rows.filter (fun r => ¬ zero r)).filter (fun r => ¬ fixed r), f r) := by
  rw [Finset.sum_filter_add_sum_filter_not, Finset.sum_filter_add_sum_filter_not]

/-! ### Cauchy over labels and rows -/

/-- Weighted Cauchy over labels: `∑ w √a √b ≤ √(∑ w a) √(∑ w b)`. -/
theorem weighted_label_cauchy {Λ : Type*} (labels : Finset Λ) (w a b : Λ → ℝ)
    (hw : ∀ x ∈ labels, 0 ≤ w x) (ha : ∀ x ∈ labels, 0 ≤ a x) (hb : ∀ x ∈ labels, 0 ≤ b x) :
    ∑ x ∈ labels, w x * (Real.sqrt (a x) * Real.sqrt (b x)) ≤
      Real.sqrt (∑ x ∈ labels, w x * a x) * Real.sqrt (∑ x ∈ labels, w x * b x) := by
  have hterm : ∀ x ∈ labels, w x * (Real.sqrt (a x) * Real.sqrt (b x)) =
      Real.sqrt (w x * a x) * Real.sqrt (w x * b x) := by
    intro x hx
    rw [Real.sqrt_mul (hw x hx), Real.sqrt_mul (hw x hx)]
    have := Real.mul_self_sqrt (hw x hx)
    calc w x * (Real.sqrt (a x) * Real.sqrt (b x))
        = (Real.sqrt (w x) * Real.sqrt (w x)) * (Real.sqrt (a x) * Real.sqrt (b x)) := by
          rw [this]
      _ = _ := by ring
  rw [Finset.sum_congr rfl hterm]
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq labels (fun x => Real.sqrt (w x * a x))
    (fun x => Real.sqrt (w x * b x))
  have hA : ∀ x ∈ labels, Real.sqrt (w x * a x)^2 = w x * a x :=
    fun x hx => Real.sq_sqrt (mul_nonneg (hw x hx) (ha x hx))
  have hB : ∀ x ∈ labels, Real.sqrt (w x * b x)^2 = w x * b x :=
    fun x hx => Real.sq_sqrt (mul_nonneg (hw x hx) (hb x hx))
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB] at hsq
  have hSA : 0 ≤ ∑ x ∈ labels, w x * a x :=
    Finset.sum_nonneg fun x hx => mul_nonneg (hw x hx) (ha x hx)
  rw [← Real.sqrt_mul hSA]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

/-- Cauchy over rows for one label: `|∑ A conj B| ≤ √(∑|A|²) √(∑|B|²)`. -/
theorem row_cauchy {R : Type*} (rows : Finset R) (A B : R → ℂ) :
    ‖∑ r ∈ rows, A r * star (B r)‖ ≤
      Real.sqrt (∑ r ∈ rows, ‖A r‖^2) * Real.sqrt (∑ r ∈ rows, ‖B r‖^2) := by
  have h1 : ‖∑ r ∈ rows, A r * star (B r)‖ ≤ ∑ r ∈ rows, ‖A r‖ * ‖B r‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [norm_mul, norm_star]
  have h2 := weighted_label_cauchy rows (fun _ => (1:ℝ)) (fun r => ‖A r‖^2) (fun r => ‖B r‖^2)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _)
  simp only [one_mul, Real.sqrt_sq (norm_nonneg _)] at h2
  exact h1.trans h2

/-- **Two-sided Cauchy over labels.** The weighted label sum of second correlations of the
two physical columns is at most the geometric mean of the two weighted one-sided energies. -/
theorem two_sided_cauchy {Λ R : Type*} (labels : Finset Λ) (rows : Λ → Finset R)
    (w : Λ → ℝ) (hw : ∀ x ∈ labels, 0 ≤ w x) (A B : Λ → R → ℂ) :
    ∑ x ∈ labels, w x * ‖∑ r ∈ rows x, A x r * star (B x r)‖ ≤
      Real.sqrt (∑ x ∈ labels, w x * ∑ r ∈ rows x, ‖A x r‖^2) *
        Real.sqrt (∑ x ∈ labels, w x * ∑ r ∈ rows x, ‖B x r‖^2) := by
  refine le_trans (Finset.sum_le_sum fun x hx =>
    mul_le_mul_of_nonneg_left (row_cauchy (rows x) (A x) (B x)) (hw x hx)) ?_
  exact weighted_label_cauchy labels w _ _ hw
    (fun x _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (fun x _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-! ### The split of one side as data -/

/-- The second-step split of one first-common side at one scale, in a side frame `F`:
`total v` is the side energy at height `v` (first artificial divisor summed inside, after
the D-Cauchy and the D⁴ transfer and their normalizations); `rL`, `rR` are the two physical
columns of the second correlation, `labels` the nonfixed second labels, and `cross x v` the
absolute label correlation. -/
structure SecondSplit (F : SideFrame) where
  total : ℝ → ℝ
  zero : ℝ → ℝ
  fixedPart : ℝ → ℝ
  tail : ℝ → ℝ
  rL : F.Src
  rR : F.Src
  labels : Finset F.Label
  cross : F.Label → ℝ → ℝ
  /-- the Poisson split (`poisson_split` plus the tail truncation) -/
  htotal : ∀ v, total v ≤ zero v + fixedPart v + (∑ x ∈ labels, F.weight x * cross x v) + tail v
  /-- Cauchy over rows inside one label (`row_cauchy`) -/
  hcross : ∀ x ∈ labels, ∀ v, cross x v ≤
    Real.sqrt (F.energy rL x v) * Real.sqrt (F.energy rR x v)
  /-- nonnegative label weights -/
  hweight : ∀ x ∈ labels, 0 ≤ F.weight x

namespace SecondSplit
variable {F : SideFrame}

/-- The nonfixed part of a split is bounded by the two weighted one-sided label energies. -/
theorem nonfixed_le (S : SecondSplit F) (v : ℝ) :
    ∑ x ∈ S.labels, F.weight x * S.cross x v ≤
      Real.sqrt (∑ x ∈ S.labels, F.weight x * F.energy S.rL x v) *
        Real.sqrt (∑ x ∈ S.labels, F.weight x * F.energy S.rR x v) := by
  refine le_trans (Finset.sum_le_sum fun x hx =>
    mul_le_mul_of_nonneg_left (S.hcross x hx v) (S.hweight x hx)) ?_
  exact weighted_label_cauchy S.labels F.weight _ _ S.hweight
    (fun x _ => F.energy_nonneg _ _ _) (fun x _ => F.energy_nonneg _ _ _)

/-- Total side energy from bounds on the four parts, the nonfixed part through two one-sided
bounds `EL`, `ER` on the weighted label energies. -/
theorem total_le (S : SecondSplit F) (v Z0 Zf Zt EL ER : ℝ)
    (h0 : S.zero v ≤ Z0) (hf : S.fixedPart v ≤ Zf) (ht : S.tail v ≤ Zt)
    (hL : ∑ x ∈ S.labels, F.weight x * F.energy S.rL x v ≤ EL)
    (hR : ∑ x ∈ S.labels, F.weight x * F.energy S.rR x v ≤ ER) :
    S.total v ≤ Z0 + Zf + Real.sqrt EL * Real.sqrt ER + Zt := by
  have hn := S.nonfixed_le v
  have hsL := Real.sqrt_le_sqrt hL
  have hsR := Real.sqrt_le_sqrt hR
  have hn' : Real.sqrt (∑ x ∈ S.labels, F.weight x * F.energy S.rL x v) *
      Real.sqrt (∑ x ∈ S.labels, F.weight x * F.energy S.rR x v) ≤
      Real.sqrt EL * Real.sqrt ER :=
    mul_le_mul hsL hsR (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith [S.htotal v]

end SecondSplit

end
end QRH.DensitySplitThird.CubeFree.Second
