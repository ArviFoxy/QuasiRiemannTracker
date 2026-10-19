/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountAvailability

set_option autoImplicit false
namespace OAI.SevenEighths.MainCount
noncomputable section

inductive Stage where
  | warmup | final
  deriving DecidableEq

def Stage.aPlane : Stage → Plane | .warmup => .A2 | .final => .A
def Stage.cPlane : Stage → Plane | .warmup => .C2 | .final => .C
def Stage.deltaLo : Stage → ℝ | .warmup => 4543/10000 | .final => 9087/20000

/-- Only the two new estimates valid at the current incumbent are used. -/
def Stage.Supports (S : Stage) (P : Plane) : Prop :=
  P=.PR62 ∨ P=.PR60 ∨ P=.oldA ∨ P=.oldC ∨ P=.oldWeak ∨
    P=S.aPlane ∨ P=S.cPlane

theorem Stage.supports_old (S : Stage) (P : Target830.Count.Plane) :
    S.Supports (Plane.ofOld P) := by
  cases P <;> simp [Stage.Supports,Plane.ofOld]

def window10 (S : Stage) : Window where
  plane := S.aPlane
  deltaLo := S.deltaLo
  deltaHi := 117/256
  pLo := 127/256
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window11 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 117/256
  deltaHi := 237/512
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window12 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 237/512
  deltaHi := 15/32
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window13 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 15/32
  deltaHi := 123/256
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window14 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 123/256
  deltaHi := 63/128
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

end
end OAI.SevenEighths.MainCount
