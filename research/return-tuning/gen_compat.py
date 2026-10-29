"""Emit Submissions/arvi_return_tuning/Compat.lean: the 31 windows of arvi_density re-certified by the kernel check."""
import os, sys
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from windows import parse_windows

OUT = '/home/user/lean-env/qrh/Submissions/arvi_return_tuning/Compat.lean'


def q(v):
    v = Fr(v)
    return f'{v.numerator}/{v.denominator}' if v.denominator != 1 else f'{v.numerator}'


ws = parse_windows()
lines = ['''import Submissions.arvi_return_tuning.Data
import Submissions.arvi_density.Return.Windows

/-!
# Compatibility check: the 31 windows of `arvi_density` re-certified by the kernel

Each `returnWindowNN'` has the data of `QRH.ArviDensity.Return.returnWindowNN` and its `certificate`
from one `decide +kernel` check of the fifteen guard polynomials (`admission_of_check`), instead of the
fifteen Bernstein identities of `Rows/AdmissionNN.lean`. `returnWindowNN' = returnWindowNN` holds by `rfl`
(the certificate is a proof), so the reflective windows are drop-in replacements. This module imports the
original windows only for that comparison; the new return (`Windows.lean`) does not.
-/

set_option autoImplicit false

namespace QRH.ArviReturnTuning.Compat
noncomputable section

open QRH.ArviDensity.Return QRH.ArviReturnTuning
''']
for w in ws:
    i = w['idx']
    b = w['branch']
    lo, hi, pl = q(w['dlo']), q(w['dhi']), q(w['plo'])
    lines.append(f'''theorem check{i:02d} : windowCheck (toQ .{b}) 0 ({lo}) ({hi}) ({pl}) = true := by decide +kernel
def returnWindow{i:02d}' : ReturnCountWindow where
  branch := .{b}
  nonold := by decide
  deltaLo := ({lo}:ℝ)
  deltaHi := ({hi}:ℝ)
  pLo := ({pl}:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .{b} (by decide) 0 ({lo}) ({hi}) ({pl}) check{i:02d}
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow{i:02d}'_eq : returnWindow{i:02d}' = returnWindow{i:02d} := rfl
''')
lines.append('''theorem returnWindows_eq : [''' + ', '.join(f"returnWindow{w['idx']:02d}'" for w in ws) + '''] = returnWindows := rfl

end
end QRH.ArviReturnTuning.Compat
''')
open(OUT, 'w').write('\n'.join(lines))
print('written', OUT)
