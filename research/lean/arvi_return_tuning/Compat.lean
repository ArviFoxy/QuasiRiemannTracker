import Submissions.arvi_return_tuning.Data
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

theorem check01 : windowCheck (toQ .capP) 0 (9/32) (3/8) (3/8) = true := by decide +kernel
def returnWindow01' : ReturnCountWindow where
  branch := .capP
  nonold := by decide
  deltaLo := (9/32:ℝ)
  deltaHi := (3/8:ℝ)
  pLo := (3/8:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capP (by decide) 0 (9/32) (3/8) (3/8) check01
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow01'_eq : returnWindow01' = returnWindow01 := rfl

theorem check02 : windowCheck (toQ .capP) 0 (9/32) (21/64) (7/16) = true := by decide +kernel
def returnWindow02' : ReturnCountWindow where
  branch := .capP
  nonold := by decide
  deltaLo := (9/32:ℝ)
  deltaHi := (21/64:ℝ)
  pLo := (7/16:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capP (by decide) 0 (9/32) (21/64) (7/16) check02
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow02'_eq : returnWindow02' = returnWindow02 := rfl

theorem check03 : windowCheck (toQ .capC) 0 (21/64) (3/8) (7/16) = true := by decide +kernel
def returnWindow03' : ReturnCountWindow where
  branch := .capC
  nonold := by decide
  deltaLo := (21/64:ℝ)
  deltaHi := (3/8:ℝ)
  pLo := (7/16:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capC (by decide) 0 (21/64) (3/8) (7/16) check03
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow03'_eq : returnWindow03' = returnWindow03 := rfl

theorem check04 : windowCheck (toQ .capP) 0 (3/8) (27/64) (3/8) = true := by decide +kernel
def returnWindow04' : ReturnCountWindow where
  branch := .capP
  nonold := by decide
  deltaLo := (3/8:ℝ)
  deltaHi := (27/64:ℝ)
  pLo := (3/8:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capP (by decide) 0 (3/8) (27/64) (3/8) check04
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow04'_eq : returnWindow04' = returnWindow04 := rfl

theorem check05 : windowCheck (toQ .capP) 0 (3/8) (51/128) (13/32) = true := by decide +kernel
def returnWindow05' : ReturnCountWindow where
  branch := .capP
  nonold := by decide
  deltaLo := (3/8:ℝ)
  deltaHi := (51/128:ℝ)
  pLo := (13/32:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capP (by decide) 0 (3/8) (51/128) (13/32) check05
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow05'_eq : returnWindow05' = returnWindow05 := rfl

theorem check06 : windowCheck (toQ .capP) 0 (51/128) (27/64) (13/32) = true := by decide +kernel
def returnWindow06' : ReturnCountWindow where
  branch := .capP
  nonold := by decide
  deltaLo := (51/128:ℝ)
  deltaHi := (27/64:ℝ)
  pLo := (13/32:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capP (by decide) 0 (51/128) (27/64) (13/32) check06
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow06'_eq : returnWindow06' = returnWindow06 := rfl

theorem check07 : windowCheck (toQ .C) 0 (27/64) (15/32) (3/8) = true := by decide +kernel
def returnWindow07' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (27/64:ℝ)
  deltaHi := (15/32:ℝ)
  pLo := (3/8:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (27/64) (15/32) (3/8) check07
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow07'_eq : returnWindow07' = returnWindow07 := rfl

theorem check08 : windowCheck (toQ .capC) 0 (3/8) (51/128) (7/16) = true := by decide +kernel
def returnWindow08' : ReturnCountWindow where
  branch := .capC
  nonold := by decide
  deltaLo := (3/8:ℝ)
  deltaHi := (51/128:ℝ)
  pLo := (7/16:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capC (by decide) 0 (3/8) (51/128) (7/16) check08
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow08'_eq : returnWindow08' = returnWindow08 := rfl

theorem check09 : windowCheck (toQ .weakC7) 0 (51/128) (27/64) (7/16) = true := by decide +kernel
def returnWindow09' : ReturnCountWindow where
  branch := .weakC7
  nonold := by decide
  deltaLo := (51/128:ℝ)
  deltaHi := (27/64:ℝ)
  pLo := (7/16:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .weakC7 (by decide) 0 (51/128) (27/64) (7/16) check09
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow09'_eq : returnWindow09' = returnWindow09 := rfl

theorem check10 : windowCheck (toQ .capC) 0 (3/8) (51/128) (15/32) = true := by decide +kernel
def returnWindow10' : ReturnCountWindow where
  branch := .capC
  nonold := by decide
  deltaLo := (3/8:ℝ)
  deltaHi := (51/128:ℝ)
  pLo := (15/32:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capC (by decide) 0 (3/8) (51/128) (15/32) check10
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow10'_eq : returnWindow10' = returnWindow10 := rfl

theorem check11 : windowCheck (toQ .weakC7) 0 (51/128) (27/64) (15/32) = true := by decide +kernel
def returnWindow11' : ReturnCountWindow where
  branch := .weakC7
  nonold := by decide
  deltaLo := (51/128:ℝ)
  deltaHi := (27/64:ℝ)
  pLo := (15/32:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .weakC7 (by decide) 0 (51/128) (27/64) (15/32) check11
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow11'_eq : returnWindow11' = returnWindow11 := rfl

theorem check12 : windowCheck (toQ .C) 0 (27/64) (15/32) (7/16) = true := by decide +kernel
def returnWindow12' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (27/64:ℝ)
  deltaHi := (15/32:ℝ)
  pLo := (7/16:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (27/64) (15/32) (7/16) check12
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow12'_eq : returnWindow12' = returnWindow12 := rfl

theorem check13 : windowCheck (toQ .C) 0 (27/64) (57/128) (15/32) = true := by decide +kernel
def returnWindow13' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (27/64:ℝ)
  deltaHi := (57/128:ℝ)
  pLo := (15/32:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (27/64) (57/128) (15/32) check13
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow13'_eq : returnWindow13' = returnWindow13 := rfl

theorem check14 : windowCheck (toQ .C) 0 (57/128) (15/32) (15/32) = true := by decide +kernel
def returnWindow14' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (57/128:ℝ)
  deltaHi := (15/32:ℝ)
  pLo := (15/32:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (57/128) (15/32) (15/32) check14
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow14'_eq : returnWindow14' = returnWindow14 := rfl

theorem check15 : windowCheck (toQ .C) 0 (57/128) (117/256) (31/64) = true := by decide +kernel
def returnWindow15' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (57/128:ℝ)
  deltaHi := (117/256:ℝ)
  pLo := (31/64:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (57/128) (117/256) (31/64) check15
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow15'_eq : returnWindow15' = returnWindow15 := rfl

theorem check16 : windowCheck (toQ .C) 0 (57/128) (231/512) (63/128) = true := by decide +kernel
def returnWindow16' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (57/128:ℝ)
  deltaHi := (231/512:ℝ)
  pLo := (63/128:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (57/128) (231/512) (63/128) check16
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow16'_eq : returnWindow16' = returnWindow16 := rfl

theorem check17 : windowCheck (toQ .C) 0 (57/128) (459/1024) (127/256) = true := by decide +kernel
def returnWindow17' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (57/128:ℝ)
  deltaHi := (459/1024:ℝ)
  pLo := (127/256:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (57/128) (459/1024) (127/256) check17
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow17'_eq : returnWindow17' = returnWindow17 := rfl

theorem check18 : windowCheck (toQ .C) 0 (459/1024) (231/512) (127/256) = true := by decide +kernel
def returnWindow18' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (459/1024:ℝ)
  deltaHi := (231/512:ℝ)
  pLo := (127/256:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (459/1024) (231/512) (127/256) check18
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow18'_eq : returnWindow18' = returnWindow18 := rfl

theorem check19 : windowCheck (toQ .C) 0 (459/1024) (921/2048) (255/512) = true := by decide +kernel
def returnWindow19' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (459/1024:ℝ)
  deltaHi := (921/2048:ℝ)
  pLo := (255/512:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (459/1024) (921/2048) (255/512) check19
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow19'_eq : returnWindow19' = returnWindow19 := rfl

theorem check20 : windowCheck (toQ .C) 0 (459/1024) (1839/4096) (511/1024) = true := by decide +kernel
def returnWindow20' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (459/1024:ℝ)
  deltaHi := (1839/4096:ℝ)
  pLo := (511/1024:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (459/1024) (1839/4096) (511/1024) check20
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow20'_eq : returnWindow20' = returnWindow20 := rfl

theorem check21 : windowCheck (toQ .C) 0 (459/1024) (3675/8192) (1023/2048) = true := by decide +kernel
def returnWindow21' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (459/1024:ℝ)
  deltaHi := (3675/8192:ℝ)
  pLo := (1023/2048:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (459/1024) (3675/8192) (1023/2048) check21
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow21'_eq : returnWindow21' = returnWindow21 := rfl

theorem check22 : windowCheck (toQ .C) 0 (3675/8192) (1839/4096) (1023/2048) = true := by decide +kernel
def returnWindow22' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (3675/8192:ℝ)
  deltaHi := (1839/4096:ℝ)
  pLo := (1023/2048:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (3675/8192) (1839/4096) (1023/2048) check22
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow22'_eq : returnWindow22' = returnWindow22 := rfl

theorem check23 : windowCheck (toQ .C) 0 (3675/8192) (7353/16384) (2047/4096) = true := by decide +kernel
def returnWindow23' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (3675/8192:ℝ)
  deltaHi := (7353/16384:ℝ)
  pLo := (2047/4096:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (3675/8192) (7353/16384) (2047/4096) check23
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow23'_eq : returnWindow23' = returnWindow23 := rfl

theorem check24 : windowCheck (toQ .C) 0 (7353/16384) (1839/4096) (2047/4096) = true := by decide +kernel
def returnWindow24' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (7353/16384:ℝ)
  deltaHi := (1839/4096:ℝ)
  pLo := (2047/4096:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (7353/16384) (1839/4096) (2047/4096) check24
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow24'_eq : returnWindow24' = returnWindow24 := rfl

theorem check25 : windowCheck (toQ .C) 0 (1839/4096) (921/2048) (511/1024) = true := by decide +kernel
def returnWindow25' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (1839/4096:ℝ)
  deltaHi := (921/2048:ℝ)
  pLo := (511/1024:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (1839/4096) (921/2048) (511/1024) check25
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow25'_eq : returnWindow25' = returnWindow25 := rfl

theorem check26 : windowCheck (toQ .C) 0 (921/2048) (231/512) (255/512) = true := by decide +kernel
def returnWindow26' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (921/2048:ℝ)
  deltaHi := (231/512:ℝ)
  pLo := (255/512:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (921/2048) (231/512) (255/512) check26
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow26'_eq : returnWindow26' = returnWindow26 := rfl

theorem check27 : windowCheck (toQ .C) 0 (231/512) (117/256) (63/128) = true := by decide +kernel
def returnWindow27' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (231/512:ℝ)
  deltaHi := (117/256:ℝ)
  pLo := (63/128:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (231/512) (117/256) (63/128) check27
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow27'_eq : returnWindow27' = returnWindow27 := rfl

theorem check28 : windowCheck (toQ .C) 0 (117/256) (15/32) (31/64) = true := by decide +kernel
def returnWindow28' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (117/256:ℝ)
  deltaHi := (15/32:ℝ)
  pLo := (31/64:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (117/256) (15/32) (31/64) check28
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow28'_eq : returnWindow28' = returnWindow28 := rfl

theorem check29 : windowCheck (toQ .C) 0 (15/32) (33/64) (7/16) = true := by decide +kernel
def returnWindow29' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (15/32:ℝ)
  deltaHi := (33/64:ℝ)
  pLo := (7/16:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (15/32) (33/64) (7/16) check29
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow29'_eq : returnWindow29' = returnWindow29 := rfl

theorem check30 : windowCheck (toQ .C) 0 (33/64) (69/128) (15/32) = true := by decide +kernel
def returnWindow30' : ReturnCountWindow where
  branch := .C
  nonold := by decide
  deltaLo := (33/64:ℝ)
  deltaHi := (69/128:ℝ)
  pLo := (15/32:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .C (by decide) 0 (33/64) (69/128) (15/32) check30
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow30'_eq : returnWindow30' = returnWindow30 := rfl

theorem check31 : windowCheck (toQ .capP) 0 (69/128) (141/256) (31/64) = true := by decide +kernel
def returnWindow31' : ReturnCountWindow where
  branch := .capP
  nonold := by decide
  deltaLo := (69/128:ℝ)
  deltaHi := (141/256:ℝ)
  pLo := (31/64:ℝ)
  deltaBounds := by norm_num
  pBounds := by norm_num
  certificate := fun hδ hp j => admission_of_check .capP (by decide) 0 (69/128) (141/256) (31/64) check31
    (by simpa using hδ) (by simpa using hp) j
theorem returnWindow31'_eq : returnWindow31' = returnWindow31 := rfl

theorem returnWindows_eq : [returnWindow01', returnWindow02', returnWindow03', returnWindow04', returnWindow05', returnWindow06', returnWindow07', returnWindow08', returnWindow09', returnWindow10', returnWindow11', returnWindow12', returnWindow13', returnWindow14', returnWindow15', returnWindow16', returnWindow17', returnWindow18', returnWindow19', returnWindow20', returnWindow21', returnWindow22', returnWindow23', returnWindow24', returnWindow25', returnWindow26', returnWindow27', returnWindow28', returnWindow29', returnWindow30', returnWindow31'] = returnWindows := rfl

end
end QRH.ArviReturnTuning.Compat
