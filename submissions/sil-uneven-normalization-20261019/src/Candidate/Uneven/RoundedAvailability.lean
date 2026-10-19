/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.RoundedRowsBase

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem critical_plane_available {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) : available 7 d p := by
  norm_num [available]
  rcases le_total d (237/512) with h₁ | h₁
  · exact Or.inl ⟨hd.1,h₁,hp⟩
  · right
    rcases le_total d (15/32) with h₂ | h₂
    · exact Or.inl ⟨h₁,h₂,hp⟩
    · right
      rcases le_total d (123/256) with h₃ | h₃
      · exact Or.inl ⟨h₂,h₃,hp⟩
      · exact Or.inr ⟨h₃,hd.2,hp⟩

end Sil.Uneven.RoundedRows
