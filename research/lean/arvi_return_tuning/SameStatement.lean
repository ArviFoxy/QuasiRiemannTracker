import Submissions.arvi_density.FinalF50
import Submissions.arvi_return_tuning.FinalF50
import Submissions.arvi_return_tuning.Compat

/-!
# Test: the reflective return proves the merged statement

Imports both returns (the merged one only for this comparison). The two top theorems have the same type
(the equality of the two proofs is `rfl` by proof irrelevance only if the propositions coincide).
-/

set_option autoImplicit false

example : @QRH.ArviReturnTuning.dirichlet_nonvanishing_f50 = @QRH.ArviDensity.dirichlet_nonvanishing_f50 := rfl

#print axioms QRH.ArviReturnTuning.dirichlet_nonvanishing_f50
#print axioms QRH.ArviDensity.Return.Tuning.FinalEdges.closed_envelope_return_cover
#print axioms QRH.ArviReturnTuning.windows_ok
#print axioms QRH.ArviReturnTuning.ev_guard
#print axioms QRH.ArviReturnTuning.coverOK_sound
#print axioms QRH.ArviReturnTuning.Compat.returnWindows_eq
