import Submissions.arvi_return_tuning.CoverQ

/-!
# The count windows of the reflective return

Five windows replace the 31 windows (and the 31 files `Rows/AdmissionNN.lean`, 465 Bernstein
identities) of `arvi_density`'s return. Each is the rational data of a branch and a rectangle
`[dlo, dhi] × [plo, 1/2]`, chosen as a maximal rectangle on which the branch is admissible
(`research/return-tuning/`); the fifteen guards of all five are certified by one kernel check.
-/

set_option autoImplicit false

namespace QRH.ArviReturnTuning

open QRH.ArviDensity.Return

/-- `(branch, dlo, dhi, plo)`: the count face `C` on the binding strip, the capped physical face on the
left part, the capped count face and the weakened count face `B - 7/4000` in between, and a small capped
physical window at the right end of the strip where the old count fails. -/
def winsQ : List WinQ :=
  [⟨.C, 27 / 64, 35 / 64, 1 / 4⟩,
   ⟨.capP, 1 / 4, 7 / 16, 1 / 4⟩,
   ⟨.capC, 21 / 64, 51 / 128, 7 / 16⟩,
   ⟨.weakC7, 51 / 128, 7 / 16, 3 / 8⟩,
   ⟨.capP, 69 / 128, 141 / 256, 31 / 64⟩]

/-- The bounds and the fifteen guards of every window (no subdivision needed). -/
theorem windows_ok : winsQ.all (WinQ.ok 0) = true := by decide +kernel

noncomputable section

/-- The windows of the return. -/
def returnWindows : List ReturnCountWindow := mkWindows 0 winsQ windows_ok

end

end QRH.ArviReturnTuning
