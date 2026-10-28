/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/fine_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
Two full source providers remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FineReturn.Facts
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FineReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

def power_oldSmall_capP (δ p : ℝ) : ℝ := (2745277421/2000000000:ℝ)*δ^0*p^0 + (-2745277421/6000000000:ℝ)*δ^0*p^1 + (-8964027421/5000000000:ℝ)*δ^1*p^0 + (-2503579021755604841/4487205480000000000:ℝ)*δ^1*p^1 + (25413941541217577/179488219200000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (99078898171217577/149573516000000000:ℝ)*δ^2*p^1 + (25553044686737303/149573516000000000:ℝ)*δ^2*p^2
theorem power_oldSmall_capP_expanded (δ p : ℝ) : rowMargin .oldSmall .capP δ p = power_oldSmall_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_capP] <;> ring

def power_oldSmall_old (δ p : ℝ) : ℝ := (2745277421/2000000000:ℝ)*δ^0*p^0 + (-582493339290786677/673080822000000000:ℝ)*δ^0*p^1 + (-8964027421/5000000000:ℝ)*δ^1*p^0 + (-316837929152975531/1682702055000000000:ℝ)*δ^1*p^1 + (95212157100109146863183/125843831373387690000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (618115310899859/934834475000000:ℝ)*δ^2*p^1 + (-758122004112923/2804503425000000:ℝ)*δ^2*p^2 + (-637087327849436/4194794379112923:ℝ)*δ^2*p^3
theorem power_oldSmall_old_expanded (δ p : ℝ) : rowMargin .oldSmall .old δ p = power_oldSmall_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_old] <;> ring

def power_oldSwitch_C (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-3103799623575821/25382406000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (1113993156190429355346997/3559252228087027500000000:ℝ)*δ^1*p^1 + (21200697354101302211189/854220534740886600000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-720688417130060807548811/711850445617405500000000:ℝ)*δ^2*p^1 + (575418752338485658894051/711850445617405500000000:ℝ)*δ^2*p^2 + (-1459390900184264/5084646040124325:ℝ)*δ^2*p^3
theorem power_oldSwitch_C_expanded (δ p : ℝ) : rowMargin .oldSwitch .C δ p = power_oldSwitch_C δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_C] <;> ring

def power_oldSwitch_Cphys (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-1066135948708207/9206402000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (1131960721259401453326197/3872907891139027500000000:ℝ)*δ^1*p^1 + (1692745117671827178491/61966526258224440000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-151329172517948140416527/154916315645561100000000:ℝ)*δ^2*p^1 + (4722163243144910640799/6196652625822444000000:ℝ)*δ^2*p^2 + (-10215736301289848/38729078911390275:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cphys_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cphys δ p = power_oldSwitch_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cphys] <;> ring

def power_oldSwitch_capP (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-253777421/6000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (19086742759082311/420675513750000000:ℝ)*δ^1*p^1 + (13646021811288047/201924246600000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-94046909708711953/168270205500000000:ℝ)*δ^2*p^1 + (37432659695161193/168270205500000000:ℝ)*δ^2*p^2
theorem power_oldSwitch_capP_expanded (δ p : ℝ) : rowMargin .oldSwitch .capP δ p = power_oldSwitch_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_capP] <;> ring

def power_oldSwitch_old (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-53846527955286677/673080822000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (245985979853524469/1682702055000000000:ℝ)*δ^1*p^1 + (82405812697460171768647/1132594482360489210000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-6245179538338769/8413510275000000:ℝ)*δ^2*p^1 + (3939467037661231/8413510275000000:ℝ)*δ^2*p^2 + (-5107868150644924/37753149412016307:ℝ)*δ^2*p^3
theorem power_oldSwitch_old_expanded (δ p : ℝ) : rowMargin .oldSwitch .old δ p = power_oldSwitch_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_old] <;> ring

def power_newSwitch_C (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-3103799623575821/25382406000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (10294813159493281/31728007500000000:ℝ)*δ^1*p^1 + (104703373241797/7614721800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-6453538639238203/6345601500000000:ℝ)*δ^2*p^1 + (5100264058190723/6345601500000000:ℝ)*δ^2*p^2 + (-88308904/317280075:ℝ)*δ^2*p^3
theorem power_newSwitch_C_expanded (δ p : ℝ) : rowMargin .newSwitch .C δ p = power_newSwitch_C δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_C] <;> ring

def power_newSwitch_Cphys (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-1066135948708207/9206402000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (10487094171974881/34524007500000000:ℝ)*δ^1*p^1 + (9299278204843/552384120000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1355328167881471/1380960300000000:ℝ)*δ^2*p^1 + (41840688443327/55238412000000:ℝ)*δ^2*p^2 + (-88308904/345240075:ℝ)*δ^2*p^3
theorem power_newSwitch_Cphys_expanded (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p = power_newSwitch_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cphys] <;> ring

def power_newSwitch_capP (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-253777421/6000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (71071651/1250000000:ℝ)*δ^1*p^1 + (114752431/1800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-845247569/1500000000:ℝ)*δ^2*p^1 + (326792089/1500000000:ℝ)*δ^2*p^2
theorem power_newSwitch_capP_expanded (δ p : ℝ) : rowMargin .newSwitch .capP δ p = power_newSwitch_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_capP] <;> ring

def power_newSwitch_old (δ p : ℝ) : ℝ := (253777421/2000000000:ℝ)*δ^0*p^0 + (-53846527955286677/673080822000000000:ℝ)*δ^0*p^1 + (-1753777421/5000000000:ℝ)*δ^1*p^0 + (265312939369149469/1682702055000000000:ℝ)*δ^1*p^1 + (661473776429981/10096212330000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2094611152456673/2804503425000000:ℝ)*δ^2*p^1 + (1300271039543327/2804503425000000:ℝ)*δ^2*p^2 + (-44154452/336540411:ℝ)*δ^2*p^3
theorem power_newSwitch_old_expanded (δ p : ℝ) : rowMargin .newSwitch .old δ p = power_newSwitch_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_old] <;> ring

def power_newTop_C (δ p : ℝ) : ℝ := (9597564467/200000000000:ℝ)*δ^0*p^0 + (-117382062054761267/2538240600000000000:ℝ)*δ^0*p^1 + (-259421728809/1000000000000:ℝ)*δ^1*p^0 + (256343483447625959743324654109/778935444544040000000000000000:ℝ)*δ^1*p^1 + (-264426388596555260175151949143/3505209500448180000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-468428792601423461557397778449/417286845291450000000000000000:ℝ)*δ^2*p^1 + (5279503434656058474273845669591/5842015834080300000000000000000:ℝ)*δ^2*p^2 + (-80837478986154300379861/292100791704015000000000:ℝ)*δ^2*p^3
theorem power_newTop_C_expanded (δ p : ℝ) : rowMargin .newTop .C δ p = power_newTop_C δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_C] <;> ring

def power_newTop_Cphys (δ p : ℝ) : ℝ := (9597564467/200000000000:ℝ)*δ^0*p^0 + (-40320011362686289/920640200000000000:ℝ)*δ^0*p^1 + (-259421728809/1000000000000:ℝ)*δ^1*p^0 + (34369154278117274004139/110476824000000000000000:ℝ)*δ^1*p^1 + (-16667061893513681287000488313/254273513356812000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-149799573157838104120139/138096030000000000000000:ℝ)*δ^2*p^1 + (234677719921356899620139/276192060000000000000000:ℝ)*δ^2*p^2 + (-80837478986154300379861/317841891696015000000000:ℝ)*δ^2*p^3
theorem power_newTop_Cphys_expanded (δ p : ℝ) : rowMargin .newTop .Cphys δ p = power_newTop_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cphys] <;> ring

def power_newTop_capP (δ p : ℝ) : ℝ := (9597564467/200000000000:ℝ)*δ^0*p^0 + (-9597564467/600000000000:ℝ)*δ^0*p^1 + (-259421728809/1000000000000:ℝ)*δ^1*p^0 + (26022872697771645577373/276192060000000000000000:ℝ)*δ^1*p^1 + (98346265669116240396457/1657152360000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-884521957413251804603543/1380960300000000000000000:ℝ)*δ^2*p^1 + (2389383822356681730491/10788752343750000000000:ℝ)*δ^2*p^2
theorem power_newTop_capP_expanded (δ p : ℝ) : rowMargin .newTop .capP δ p = power_newTop_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_capP] <;> ring

def power_newTop_old (δ p : ℝ) : ℝ := (9597564467/200000000000:ℝ)*δ^0*p^0 + (-2036412543474391979/67308082200000000000:ℝ)*δ^0*p^1 + (-259421728809/1000000000000:ℝ)*δ^1*p^0 + (4412186814247283448764062195043/24786610503289776000000000000000:ℝ)*δ^1*p^1 + (1690993763732455477338059020957/74359831509869328000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-17256147010250971253085635659681/20655508752741480000000000000000:ℝ)*δ^2*p^1 + (3516622739985827985527995446773/6885169584247160000000000000000:ℝ)*δ^2*p^2 + (-80837478986154300379861/619665262582244400000000:ℝ)*δ^2*p^3
theorem power_newTop_old_expanded (δ p : ℝ) : rowMargin .newTop .old δ p = power_newTop_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_old] <;> ring

end
end Qrh.JointDetector.FineReturn.FinalEdges
