import Submissions.arvi_followup.Faceless.Gen.Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.RepeatedMarks.Faceless

def tree_p3_high_1_02 : IPoly.UTreeI :=
  (.leaf [[(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)]])

theorem p3_high_1_02 : certI (piece3.highU (piece3.endP 1) (0, 2)) tree_p3_high_1_02 = true := by
  decide +kernel

end QRH.RepeatedMarks.Faceless
