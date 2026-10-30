import Submissions.arvi_kwall.Closure

/-!
# The K-wall is exactly the dilution of the sextic sieve's excess

Research file (QRH, RIP program). `Closure.lean` shows that with the full-family initial bound Θ₆ the
amplify–reflect rules cannot pass slope 1/2 (the balanced-point bound stays at 7/6). Here: if the
initial bound on a thin row set (density B^{-δ}) has its excess over the diagonal reduced by δ,
`n x ≤ max (max 1 x) (theta6 x - δ)`, then amplification alone gives the fixed point
`n x ≤ 1 - δ + δ x` on `[0, 1]` for every `δ ≥ 1/6`, far beyond the square-root barrier δ = 1/2.
-/

namespace QRH.ArviKWall

/-- The diluted initial bound: the excess of Θ₆ over `max 1 x` shrinks by the density exponent `δ`. -/
noncomputable def theta6Diluted (δ x : ℝ) : ℝ := max (max 1 x) (theta6 x - δ)

/-- At the balanced point the diluted bound is the diagonal once `δ ≥ 1/6`. -/
theorem theta6Diluted_one {δ : ℝ} (hδ : 1/6 ≤ δ) : theta6Diluted δ 1 = 1 := by
  have h7 : theta6 1 = 7/6 := by unfold theta6; norm_num
  unfold theta6Diluted
  rw [h7, max_self]
  exact max_eq_left (by linarith)

/-- **Dilution breaks the K-wall.** With the diluted initial bound and the amplification rule,
the selected norm is at its fixed point `1 - δ + δ x` on `[0, 1]` for `1/6 ≤ δ`. -/
theorem fixed_point_of_dilution {δ : ℝ} (hδ : 1/6 ≤ δ) (n : ℝ → ℝ)
    (init : ∀ x, 0 ≤ x → n x ≤ theta6Diluted δ x)
    (amp : ∀ x y, 0 ≤ x → x ≤ y → n x ≤ n y - δ * (y - x)) :
    ∀ x, 0 ≤ x → x ≤ 1 → n x ≤ 1 - δ + δ * x := by
  intro x hx0 hx1
  have h1 : n 1 ≤ 1 := (init 1 zero_le_one).trans (theta6Diluted_one hδ).le
  have h2 := amp x 1 hx0 hx1
  linarith

/-- The contrast, from `Closure.lean`: without dilution the same rules allow `7/6` at the balanced point
for every slope in `[1/3, 1/2)`. The whole K-wall is the gap between `theta6` and `theta6Diluted`. -/
theorem kwall_is_dilution {δ : ℝ} (hδ : 1/3 ≤ δ) (hδ2 : δ < 1/2) :
    (∃ n : ℝ → ℝ, Rules δ n ∧ n 1 = 7/6) ∧
    (∀ n : ℝ → ℝ, (∀ x, 0 ≤ x → n x ≤ theta6Diluted δ x) →
      (∀ x y, 0 ≤ x → x ≤ y → n x ≤ n y - δ * (y - x)) → n 1 ≤ 1) := by
  refine ⟨⟨nstar δ, nstar_rules hδ hδ2, ?_⟩, fun n hinit hamp => ?_⟩
  · unfold nstar frow; norm_num
  · have := fixed_point_of_dilution (by linarith) n hinit hamp 1 zero_le_one le_rfl
    linarith

end QRH.ArviKWall

#print axioms QRH.ArviKWall.fixed_point_of_dilution
#print axioms QRH.ArviKWall.kwall_is_dilution
