/- Copyright (c) 2026 Sil, ArviFoxy. Apache-2.0.
The marked density-split leaf price.

The HIGH energy of the density-split leaf with the repeated-mark class count (PR 76) is
`Z^{ρ(ν) M + ν (P+s) - gainC ν B₀ L₀ c₀ s M}`, so its excess over `M` is the unmarked excess
`highTerm ν P s M = ν(P+s) - (1-ρ(ν)) M` reduced by the gain:

* `highTermM B₀ L₀ c₀ ν P s M = ν(P+s) - (1-ρ(ν)) M - gainC ν B₀ L₀ c₀ s M`;
* `highSupM B₀ L₀ c₀ q P s M = sup_{ν ∈ [q,3/4]} highTermM`;
* `markedDensityPrice = max (q·deletionNeed) (highSupM …)` with the clipped cut `q = densQ`.

The axioms of `Price` follow from the gain lemmas of PR 76 (`weighted_exponent_mono_rm`,
`gain_mono_rm`, `gain_row_loss_rm`, `gainC_nonneg`), valid for `1/2 ≤ ν ≤ 3/4` on the parent range
`22/23 ≤ B₀ ≤ 1`, `1 < L₀`, `0 ≤ c₀ ≤ 1`.

Fork of Sil's `Density/Price` (PR 83), in the version of this package with the floor `qf`: the HIGH
term `highTerm` is replaced by `highTermM`. -/
import Submissions.arvi_density.Density.Price
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC

set_option autoImplicit false
namespace QRH.ArviDensity.Density
noncomputable section
open QRH.ArviDensity QRH.SilDensitySplit.CubeFree QRH.ArviDensity.Hybrid

/-- The marked HIGH excess: `highTerm` reduced by the repeated-mark gain. -/
def highTermM (B₀ L₀ c₀ ν P s M : ℝ) : ℝ :=
  highTerm ν P s M - QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ s M

theorem highTermM_eq (B₀ L₀ c₀ ν P s M : ℝ) :
    highTermM B₀ L₀ c₀ ν P s M =
      ν * (P + s) - 10 * ν / (15 - 6 * ν) * M -
        QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ s M := by
  unfold highTermM highTerm; ring

theorem highTermM_eq_rho (B₀ L₀ c₀ ν P s M : ℝ) :
    highTermM B₀ L₀ c₀ ν P s M =
      (rhoOf ν - 1) * M + ν * (P + s) - QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ s M := by
  unfold highTermM; rw [highTerm_eq_rho]

theorem highTermM_le_highTerm (B₀ L₀ c₀ ν P s M : ℝ) :
    highTermM B₀ L₀ c₀ ν P s M ≤ highTerm ν P s M := by
  unfold highTermM
  linarith [QRH.RepeatedMarks.Source.gainC_nonneg ν B₀ L₀ c₀ s M]

/-- The marked HIGH price: supremum of `highTermM` over `ν ∈ [q, 3/4]`. -/
def highSupM (B₀ L₀ c₀ q P s M : ℝ) : ℝ :=
  ⨆ ν : Set.Icc q (3/4 : ℝ), highTermM B₀ L₀ c₀ ν P s M

section HighSupM
variable {q : ℝ}

theorem highSupM_bdd (B₀ L₀ c₀ : ℝ) (hq : 0 ≤ q) (P s M : ℝ) :
    BddAbove (Set.range fun ν : Set.Icc q (3/4 : ℝ) => highTermM B₀ L₀ c₀ ν P s M) := by
  refine ⟨|P + s| + |M|, ?_⟩
  rintro _ ⟨ν, rfl⟩
  exact (highTermM_le_highTerm B₀ L₀ c₀ ν P s M).trans
    (highTerm_le_abs (hq.trans ν.2.1) ν.2.2 P s M)

theorem le_highSupM (B₀ L₀ c₀ : ℝ) (hq : 0 ≤ q) {ν : ℝ} (h1 : q ≤ ν) (h2 : ν ≤ 3/4)
    (P s M : ℝ) : highTermM B₀ L₀ c₀ ν P s M ≤ highSupM B₀ L₀ c₀ q P s M :=
  le_ciSup (f := fun ν : Set.Icc q (3/4 : ℝ) => highTermM B₀ L₀ c₀ ν P s M)
    (highSupM_bdd B₀ L₀ c₀ hq P s M) ⟨ν, h1, h2⟩

theorem highSupM_le (B₀ L₀ c₀ : ℝ) (hq : q ≤ 3/4) {P s M a : ℝ}
    (h : ∀ ν, q ≤ ν → ν ≤ 3/4 → highTermM B₀ L₀ c₀ ν P s M ≤ a) :
    highSupM B₀ L₀ c₀ q P s M ≤ a := by
  have : Nonempty (Set.Icc q (3/4 : ℝ)) := ⟨⟨3/4, hq, le_rfl⟩⟩
  exact ciSup_le fun ν => h ν ν.2.1 ν.2.2

theorem highSupM_le_add (B₀ L₀ c₀ : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 3/4) {P s M P' s' M' e : ℝ}
    (h : ∀ ν, q ≤ ν → ν ≤ 3/4 → highTermM B₀ L₀ c₀ ν P' s' M' ≤ highTermM B₀ L₀ c₀ ν P s M + e) :
    highSupM B₀ L₀ c₀ q P' s' M' ≤ highSupM B₀ L₀ c₀ q P s M + e :=
  highSupM_le B₀ L₀ c₀ hq fun ν h1 h2 => by
    have := le_highSupM B₀ L₀ c₀ hq0 h1 h2 P s M
    linarith [h ν h1 h2]

end HighSupM

/-! ### The gain lemmas at the parent range -/

section Terms
variable {B₀ L₀ c₀ ν : ℝ}

/-- Monotonicity of the marked excess in the ordinary width and the retained width. -/
theorem highTermM_mono (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hL : 1 < L₀) {P P' s s' M : ℝ}
    (hP : P' ≤ P) (hs : s' ≤ s) :
    highTermM B₀ L₀ c₀ ν P' s' M ≤ highTermM B₀ L₀ c₀ ν P s M := by
  have h := QRH.Record1252270103Source.High.weighted_exponent_mono_rm (B := B₀) (h := c₀) (Q := M)
    hν0 hν1 hL hs
  unfold highTermM highTerm
  nlinarith

/-- The marked excess grows at most with slope `1` in the retained width. -/
theorem highTermM_lipS (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1)
    (hL : 1 < L₀) (hc0 : 0 ≤ c₀) (hc1 : c₀ ≤ 1) {P s M δ : ℝ} (hδ : 0 ≤ δ) :
    highTermM B₀ L₀ c₀ ν P (s + δ) M ≤ highTermM B₀ L₀ c₀ ν P s M + δ := by
  have h := QRH.Record1252270103Source.High.gain_mono_rm hν0 hν1 hB0 hB1 hL hc0 hc1
    (show s ≤ s + δ by linarith) (le_refl M)
  unfold highTermM highTerm
  nlinarith

/-- The marked excess is Lipschitz with constant `1` in the envelope. -/
theorem highTermM_lipM (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1)
    (hL : 1 < L₀) (hc0 : 0 ≤ c₀) (hc1 : c₀ ≤ 1) {P s M δ : ℝ} :
    highTermM B₀ L₀ c₀ ν P s (M + δ) ≤ highTermM B₀ L₀ c₀ ν P s M + |δ| := by
  have hd : 0 < 15 - 6 * ν := by linarith
  have hk0 : 0 ≤ 10 * ν / (15 - 6 * ν) := div_nonneg (by linarith) hd.le
  rcases le_total 0 δ with hδ | hδ
  · have h := QRH.Record1252270103Source.High.gain_mono_rm hν0 hν1 hB0 hB1 hL hc0 hc1
      (le_refl s) (show M ≤ M + δ by linarith)
    rw [abs_of_nonneg hδ]
    unfold highTermM highTerm
    nlinarith
  · have h := QRH.Record1252270103Source.High.gain_row_loss_rm (S := s) hν0 hν1 hB0 hB1 hL hc0 hc1
      (show M + δ ≤ M by linarith)
    have hc : QRH.Record1252270103Source.High.cmax ν =
        ν - 10 * ν / (15 - 6 * ν) := by
      rw [QRH.RepeatedMarks.Source.cmax_eq]
      simp only [QRH.RepeatedMarks.baseXi, QRH.RepeatedMarks.densityDenom]
      field_simp
    rw [hc] at h
    rw [abs_of_nonpos hδ]
    unfold highTermM highTerm
    nlinarith

end Terms

/-- The density-split price with the marked HIGH count:
`max (q(w)·deletionNeed) (sup_{ν∈[q(w),3/4]} highTermM)` with the clipped cut
`q(w) = densQ qf …`, on the parent range `22/23 ≤ B₀ ≤ 1`, `1 < L₀`, `0 ≤ c₀ < 1`. -/
def markedDensityPrice (qf B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 1 < L₀)
    (hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1) (hqf0 : 1/2 ≤ qf) (hqf1 : qf ≤ 3/4) :
    Price where
  f w P s M := max (lowPart B₀ L₀ c₀ (densQ qf B₀ L₀ L A D s₀ w) P s M)
    (highSupM B₀ L₀ c₀ (densQ qf B₀ L₀ L A D s₀ w) P s M)
  nonneg w P s M := le_max_of_le_left
    (mul_nonneg (densQ_nonneg qf B₀ L₀ L A D s₀ w (by linarith)) (deletionNeed_nonneg _ _ _ _ _ _))
  mono w P P' s s' M hP hs := by
    have hq0 := densQ_nonneg qf B₀ L₀ L A D s₀ w (by linarith)
    have hq1 := densQ_le qf B₀ L₀ L A D s₀ w hqf1
    have hqf : qf ≤ densQ qf B₀ L₀ L A D s₀ w := densQ_ge _ _ _ _ _ _ _ _
    apply max_le_max
    · exact mul_le_mul_of_nonneg_left (deletionNeed_mono (zero_lt_one.trans hL) hP hs) hq0
    · have := highSupM_le_add B₀ L₀ c₀ (e := 0) hq0 hq1 (P := P) (s := s) (M := M) (P' := P')
        (s' := s') (M' := M) (fun ν h1 h2 => by
          have hmono := highTermM_mono (B₀ := B₀) (L₀ := L₀) (c₀ := c₀) (ν := ν) (M := M)
            (by linarith : 1/2 ≤ ν) h2 hL hP hs
          linarith)
      linarith
  lip := needLip B₀ L₀ c₀
  lip_nonneg := zero_le_one.trans (one_le_needLip _ _ _)
  lipP w P s M δ hδ := by
    have hq0 := densQ_nonneg qf B₀ L₀ L A D s₀ w (by linarith)
    have hq1 := densQ_le qf B₀ L₀ L A D s₀ w hqf1
    have hqf : qf ≤ densQ qf B₀ L₀ L A D s₀ w := densQ_ge _ _ _ _ _ _ _ _
    have hK := one_le_needLip B₀ L₀ c₀
    have hKδ : δ ≤ needLip B₀ L₀ c₀ * δ := by nlinarith
    apply max_le_max_add
    · exact lowPart_lip hq0 (by linarith) (by nlinarith)
        (deletionNeed_lipP (zero_lt_one.trans hL) hδ)
    · refine highSupM_le_add B₀ L₀ c₀ hq0 hq1 fun ν h1 h2 => ?_
      unfold highTermM highTerm
      have : ν * δ ≤ δ := by nlinarith
      nlinarith
  lipS w P s M δ hδ := by
    have hq0 := densQ_nonneg qf B₀ L₀ L A D s₀ w (by linarith)
    have hq1 := densQ_le qf B₀ L₀ L A D s₀ w hqf1
    have hqf : qf ≤ densQ qf B₀ L₀ L A D s₀ w := densQ_ge _ _ _ _ _ _ _ _
    have hK := one_le_needLip B₀ L₀ c₀
    have hKδ : δ ≤ needLip B₀ L₀ c₀ * δ := by nlinarith
    apply max_le_max_add
    · exact lowPart_lip hq0 (by linarith) (by nlinarith)
        (deletionNeed_lipS (zero_lt_one.trans hL) hδ)
    · refine highSupM_le_add B₀ L₀ c₀ hq0 hq1 fun ν h1 h2 => ?_
      have := highTermM_lipS (c₀ := c₀) (P := P) (s := s) (M := M) (by linarith : 1/2 ≤ ν) h2
        hface.1 hface.2.1 hL hface.2.2.1 hface.2.2.2.le hδ
      linarith
  lipM w P s M δ := by
    have hq0 := densQ_nonneg qf B₀ L₀ L A D s₀ w (by linarith)
    have hq1 := densQ_le qf B₀ L₀ L A D s₀ w hqf1
    have hqf : qf ≤ densQ qf B₀ L₀ L A D s₀ w := densQ_ge _ _ _ _ _ _ _ _
    have hK := one_le_needLip B₀ L₀ c₀
    have hδ := abs_nonneg δ
    have hKδ : |δ| ≤ needLip B₀ L₀ c₀ * |δ| := by nlinarith
    apply max_le_max_add
    · exact lowPart_lip hq0 (by linarith) (by nlinarith) (deletionNeed_lipM (zero_lt_one.trans hL))
    · refine highSupM_le_add B₀ L₀ c₀ hq0 hq1 fun ν h1 h2 => ?_
      have := highTermM_lipM (c₀ := c₀) (P := P) (s := s) (M := M) (δ := δ)
        (by linarith : 1/2 ≤ ν) h2 hface.1 hface.2.1 hL hface.2.2.1 hface.2.2.2.le
      linarith

theorem markedDensityPrice_f (qf B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 1 < L₀)
    (hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1) (hqf0 : 1/2 ≤ qf) (hqf1 : qf ≤ 3/4)
    (w P s M : ℝ) :
    (markedDensityPrice qf B₀ L₀ c₀ L A D s₀ hL hface hqf0 hqf1).f w P s M =
      max (densQ qf B₀ L₀ L A D s₀ w * deletionNeed B₀ L₀ c₀ P s M)
        (highSupM B₀ L₀ c₀ (densQ qf B₀ L₀ L A D s₀ w) P s M) := rfl

theorem markedDensityPrice_lip (qf B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 1 < L₀)
    (hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1) (hqf0 : 1/2 ≤ qf) (hqf1 : qf ≤ 3/4) :
    (markedDensityPrice qf B₀ L₀ c₀ L A D s₀ hL hface hqf0 hqf1).lip = needLip B₀ L₀ c₀ := rfl

/-- The marked price never exceeds the unmarked density price. -/
theorem markedDensityPrice_le (qf B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 1 < L₀)
    (hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1) (hqf0 : 1/2 ≤ qf) (hqf1 : qf ≤ 3/4)
    (w P s M : ℝ) :
    (markedDensityPrice qf B₀ L₀ c₀ L A D s₀ hL hface hqf0 hqf1).f w P s M ≤
      (densityPrice qf B₀ L₀ c₀ L A D s₀ (zero_lt_one.trans hL) (by linarith) hqf1).f w P s M := by
  rw [markedDensityPrice_f, densityPrice_f]
  apply max_le_max le_rfl
  have hq0 := densQ_nonneg qf B₀ L₀ L A D s₀ w (by linarith)
  have hq1 := densQ_le qf B₀ L₀ L A D s₀ w hqf1
  exact highSupM_le B₀ L₀ c₀ hq1 fun ν h1 h2 =>
    (highTermM_le_highTerm B₀ L₀ c₀ ν P s M).trans (le_highSup hq0 h1 h2 P s M)

end
end QRH.ArviDensity.Density
