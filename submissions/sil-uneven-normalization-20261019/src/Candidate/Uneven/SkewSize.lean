/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.SkewCone

set_option autoImplicit false
namespace SkewNormalization
noncomputable section

theorem clip_abs_le {s r R : ℝ} (hs : 0 ≤ s) (hr : |r| ≤ R) :
    |clip s r| ≤ R := by
  obtain ⟨hr0,hr1⟩ := abs_le.mp hr
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  unfold clip
  simp only [max_def,min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

theorem skew_abs_le_tenth {c d r p B : ℝ}
    (hc : 0 ≤ c ∧ c ≤ B) (hd : 0 ≤ d ∧ d ≤ B)
    (hs : 0 ≤ surplus c d r p) : |skew c d r p| ≤ B/10 := by
  apply clip_abs_le hs
  rw [abs_le]
  constructor <;> linarith [hc.1,hc.2,hd.1,hd.2]

end
end SkewNormalization
#print axioms SkewNormalization.skew_abs_le_tenth
