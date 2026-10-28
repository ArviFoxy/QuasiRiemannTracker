/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/fine_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
Two full source providers remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FineReturn.PowerRows
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FineReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

def row224_coefficients : Fin 3 → Fin 4 → ℝ := ![![(406278390201480371218/266208723544921875:ℝ), (674701975603157849867/266208723544921875:ℝ), (459342584709845728963/425933957671875000:ℝ), (199405203628585661/8764073203125000:ℝ)],
![(832923024857530658468/266208723544921875:ℝ), (1369510929599230959892/266208723544921875:ℝ), (113556971540065050601/53241744708984375:ℝ), (57438743952931501/3286527451171875:ℝ)],
![(3433349501908402298/2129669788359375:ℝ), (5607738005725318846/2129669788359375:ℝ), (2286154460441916548/2129669788359375:ℝ), (0:ℝ)]]
theorem row224_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (23557856028539032331/918979682304000000000:ℝ) row224_coefficients
      (57/128:ℝ) (15/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row224_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row224_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row224_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row224_coefficients]

def row225_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21649165118385542747/539437617187500:ℝ), (22634209227615199621/269718808593750:ℝ), (326047168849763142041/6473251406250000:ℝ), (42018387913674864101/6473251406250000:ℝ)],
![(3340327229054562956/44953134765625:ℝ), (60016829432878793294/404578212890625:ℝ), (64673787607025272427/809156425781250:ℝ), (4608718628999819047/809156425781250:ℝ)],
![(37863765173868089/1078875234375:ℝ), (217040400030573469/3236625703125:ℝ), (103780262898969202/3236625703125:ℝ), (0:ℝ)]]
theorem row225_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (11029518514632254033/603350761472000000000:ℝ) row225_coefficients
      (57/128:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row225_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row225_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row225_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row225_coefficients]

def row226_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141141503293826533601/809156425781250:ℝ), (161714253663555162967/404578212890625:ℝ), (60727457773015153559/215775046875000:ℝ), (20162775557235237117/359625078125000:ℝ)],
![(117557989896150945688/404578212890625:ℝ), (250978706248401206492/404578212890625:ℝ), (30759136469411214959/80915642578125:ℝ), (2255146208575645999/44953134765625:ℝ)],
![(132164153840202226/1078875234375:ℝ), (774356332965943226/3236625703125:ℝ), (378195029835336548/3236625703125:ℝ), (0:ℝ)]]
theorem row226_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (39161918289521432657/2413403045888000000000:ℝ) row226_coefficients
      (57/128:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row226_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row226_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row226_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row226_coefficients]

def row227_coefficients : Fin 3 → Fin 4 → ℝ := ![![(122037440469239291851/134859404296875:ℝ), (305026166982738558682/134859404296875:ℝ), (2943565386856449000857/1618312851562500:ℝ), (149510246694194059777/323662570312500:ℝ)],
![(151342217421761456/115166015625:ℝ), (1223368690545889453496/404578212890625:ℝ), (860294330055497919958/404578212890625:ℝ), (33702439838926292278/80915642578125:ℝ)],
![(492392910380268644/1078875234375:ℝ), (2918756074081071604/3236625703125:ℝ), (1441908501330265672/3236625703125:ℝ), (0:ℝ)]]
theorem row227_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (147415306088455693553/9653612183552000000000:ℝ) row227_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row227_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row227_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row227_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row227_coefficients]

def row228_coefficients : Fin 3 → Fin 4 → ℝ := ![![(79447633548058294354/14872503515625:ℝ), (15946806115914937620724/1115437763671875:ℝ), (28080133711852364447531/2230875527343750:ℝ), (128626069196761938241/35410722656250:ℝ)],
![(1504972026838934015392/223087552734375:ℝ), (18678555193924372665424/1115437763671875:ℝ), (14829124480270190529668/1115437763671875:ℝ), (58336404288692268908/17705361328125:ℝ)],
![(3121112509707464168/1784700421875:ℝ), (1476965900471426648/424928671875:ℝ), (15411714836532638768/8923502109375:ℝ), (0:ℝ)]]
theorem row228_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (71355131834972843191/5069596524544000000000:ℝ) row228_coefficients
      (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row228_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row228_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row228_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row228_coefficients]

def row229_coefficients : Fin 3 → Fin 4 → ℝ := ![![(40071537481037907302732/1115437763671875:ℝ), (112674999175785005668232/1115437763671875:ℝ), (105179057794769442102203/1115437763671875:ℝ), (4653640574800675444529/159348251953125:ℝ)],
![(44717083848408701261632/1115437763671875:ℝ), (16991010752342385280096/159348251953125:ℝ), (103814672275460950995848/1115437763671875:ℝ), (29594444907120080296808/1115437763671875:ℝ)],
![(61262144347631190928/8923502109375:ℝ), (122139573696763017712/8923502109375:ℝ), (6764269202700202976/991500234375:ℝ), (0:ℝ)]]
theorem row229_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (5898108973594545092219/425846108061696000000000:ℝ) row229_coefficients
      (57/128:ℝ) (15/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row229_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row229_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row229_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row229_coefficients]

def row230_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4459730006113198437967/123937529296875:ℝ), (3227431555460031430229/31869650390625:ℝ), (35183611458068716029952/371812587890625:ℝ), (32728187911706218348544/1115437763671875:ℝ)],
![(6388373852849742279544/159348251953125:ℝ), (27228460195598600632/254957203125:ℝ), (104184241238478203518976/1115437763671875:ℝ), (29778108902329646710784/1115437763671875:ℝ)],
![(12099337650262492528/1784700421875:ℝ), (40203880643211853712/2974500703125:ℝ), (60115947153493098496/8923502109375:ℝ), (0:ℝ)]]
theorem row230_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (16867742333408521/1237694464000000000:ℝ) row230_coefficients
      (57/128:ℝ) (15/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row230_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row230_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row230_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row230_coefficients]

def row231_coefficients : Fin 3 → Fin 4 → ℝ := ![![(433821225998737738831/1064834894179687500:ℝ), (714924865496227210493/1064834894179687500:ℝ), (299726922335801923243/1064834894179687500:ℝ), (57438743952931501/13146109804687500:ℝ)],
![(459235576618307654863/532417447089843750:ℝ), (747348437328325962101/532417447089843750:ℝ), (151740339872977903619/266208723544921875:ℝ), (0:ℝ)],
![(98949227913575514179/212966978835937500:ℝ), (804405196038791696609/1064834894179687500:ℝ), (655057396700762551241/2129669788359375000:ℝ), (23828171356441973/26292219609375000:ℝ)]]
theorem row231_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (230926022025202871729/9189796823040000000000:ℝ) row231_coefficients
      (15/32:ℝ) (33/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row231_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row231_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row231_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row231_coefficients]

def row232_coefficients : Fin 3 → Fin 4 → ℝ := ![![(143046360595894988563/13146109804687500:ℝ), (2719174505868206417201/118314988242187500:ℝ), (554127677572457318567/39438329414062500:ℝ), (229073467259095435567/118314988242187500:ℝ)],
![(130639591902061784347/6573054902343750:ℝ), (2313346262371844948417/59157494121093750:ℝ), (238602985722459590243/11831498824218750:ℝ), (53717457910571561921/59157494121093750:ℝ)],
![(133213034408557517431/13146109804687500:ℝ), (2298217626908758667033/118314988242187500:ℝ), (550589303112511130077/59157494121093750:ℝ), (0:ℝ)]]
theorem row232_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1455489400495437620791/73518374584320000000000:ℝ) row232_coefficients
      (15/32:ℝ) (33/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row232_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row232_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row232_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row232_coefficients]

def row233_coefficients : Fin 3 → Fin 4 → ℝ := ![![(53737975297068101113/1078875234375000:ℝ), (379861514774643708017/3236625703125000:ℝ), (280821188991992038517/3236625703125000:ℝ), (6898978945672514871/359625078125000:ℝ)],
![(124344176859205750963/1618312851562500:ℝ), (265082268760812908033/1618312851562500:ℝ), (162327339215548162927/1618312851562500:ℝ), (2388686528521222873/179812539062500:ℝ)],
![(108068983353912445487/3236625703125000:ℝ), (210543735034156985849/3236625703125000:ℝ), (5698607060734418909/179812539062500:ℝ), (0:ℝ)]]
theorem row233_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (721147555279376019301/48268060917760000000000:ℝ) row233_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row233_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row233_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row233_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row233_coefficients]

def row234_coefficients : Fin 3 → Fin 4 → ℝ := ![![(89633860617883842191/323662570312500:ℝ), (231082078870117871773/323662570312500:ℝ), (194160889551347723473/323662570312500:ℝ), (52704392339363693891/323662570312500:ℝ)],
![(285798776071972699027/809156425781250:ℝ), (661730722324967806369/809156425781250:ℝ), (470987243033807115407/809156425781250:ℝ), (19001952500437401613/161831285156250:ℝ)],
![(199806061045208675599/1618312851562500:ℝ), (131422776316395648691/539437617187500:ℝ), (97256177805232885237/809156425781250:ℝ), (0:ℝ)]]
theorem row234_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (536956832014459080321/38614448734208000000000:ℝ) row234_coefficients
      (15/32:ℝ) (33/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row234_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row234_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row234_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row234_coefficients]

def row235_coefficients : Fin 3 → Fin 4 → ℝ := ![![(479297994711064587881/269718808593750:ℝ), (3953204827067014872929/809156425781250:ℝ), (3597095085662015987429/809156425781250:ℝ), (360587848442939959381/269718808593750:ℝ)],
![(763845187354667918083/404578212890625:ℝ), (76784786040380462873/16183128515625:ℝ), (1552489263718933989151/404578212890625:ℝ), (132230677641592611803/134859404296875:ℝ)],
![(383806137345919885823/809156425781250:ℝ), (762393700816828116521/809156425781250:ℝ), (63102101220691996783/134859404296875:ℝ), (0:ℝ)]]
theorem row235_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (10355330502943261720597/772288974684160000000000:ℝ) row235_coefficients
      (15/32:ℝ) (33/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row235_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row235_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row235_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row235_coefficients]

def row236_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5079123431721681193843/404578212890625:ℝ), (14533761395813930875529/404578212890625:ℝ), (13834457788192260702029/404578212890625:ℝ), (4379809475400323520343/404578212890625:ℝ)],
![(4677674764211026045814/404578212890625:ℝ), (12583371632854676205746/404578212890625:ℝ), (445726136710729138942/16183128515625:ℝ), (3237433781985265813618/404578212890625:ℝ)],
![(752069250406401681271/404578212890625:ℝ), (166553615174544564713/44953134765625:ℝ), (746925808091121276146/404578212890625:ℝ), (0:ℝ)]]
theorem row236_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (40669252761366645201117/3089155898736640000000000:ℝ) row236_coefficients
      (15/32:ℝ) (33/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row236_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row236_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row236_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row236_coefficients]

def row237_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5121616885029408141364/404578212890625:ℝ), (14669821293096934283092/404578212890625:ℝ), (4659688725578674724864/134859404296875:ℝ), (492316824440978948096/44953134765625:ℝ)],
![(944209720248687011132/80915642578125:ℝ), (12732293731917874134284/404578212890625:ℝ), (11310807803379459801088/404578212890625:ℝ), (1099846635188569407488/134859404296875:ℝ)],
![(82423045514342735669/44953134765625:ℝ), (1478496420796132586917/404578212890625:ℝ), (736701533093669840896/404578212890625:ℝ), (0:ℝ)]]
theorem row237_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (2436977865706638219/188547112960000000000:ℝ) row237_coefficients
      (15/32:ℝ) (33/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row237_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row237_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row237_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row237_coefficients]

def row238_coefficients : Fin 3 → Fin 4 → ℝ := ![![(987562197255883341977/532417447089843750:ℝ), (1603020146437967993779/532417447089843750:ℝ), (324633575530573575901/266208723544921875:ℝ), (0:ℝ)],
![(1023072760205453258009/266208723544921875:ℝ), (1660076905148433728287/266208723544921875:ℝ), (1346630339331145240369/532417447089843750:ℝ), (23828171356441973/6573054902343750:ℝ)],
![(1063631429320023174041/532417447089843750:ℝ), (345890051459616590849/106483489417968750:ℝ), (2830041275468535523043/2129669788359375000:ℝ), (26002038298674763/2921357734375000:ℝ)]]
theorem row238_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (463782125930277543271/18379593646080000000000:ℝ) row238_coefficients
      (33/64:ℝ) (69/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row238_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row238_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row238_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row238_coefficients]

def row239_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2451552077264606875679/59157494121093750:ℝ), (4757587627549232019829/59157494121093750:ℝ), (2363509586181759206071/59157494121093750:ℝ), (53717457910571561921/59157494121093750:ℝ)],
![(494942611964613694687/5915749412109375:ℝ), (948491798417229147689/5915749412109375:ℝ), (454334652758896703002/5915749412109375:ℝ), (0:ℝ)],
![(2565284992783010289041/59157494121093750:ℝ), (4922680160639697050761/59157494121093750:ℝ), (1579068554844071320441/39438329414062500:ℝ), (14203635616809187883/118314988242187500:ℝ)]]
theorem row239_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (347168757802482166513/17644409900236800000000:ℝ) row239_coefficients
      (33/64:ℝ) (69/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row239_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row239_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row239_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row239_coefficients]

def row240_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3117553527905510140553/19719164707031250:ℝ), (3849710580269882636749/11831498824218750:ℝ), (10822565709384091689413/59157494121093750:ℝ), (102546312640516269703/6573054902343750:ℝ)],
![(8922920920431957926291/29578747060546875:ℝ), (17682069706117939718833/29578747060546875:ℝ), (8993601579934363075643/29578747060546875:ℝ), (25613940301886114789/3286527451171875:ℝ)],
![(8979735462899194677823/59157494121093750:ℝ), (650000624938296712523/2191018300781250:ℝ), (4287193628517916092649/29578747060546875:ℝ), (0:ℝ)]]
theorem row240_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (20170276880021491792103/1176293993349120000000000:ℝ) row240_coefficients
      (33/64:ℝ) (69/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row240_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row240_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row240_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row240_coefficients]

def row241_coefficients : Fin 3 → Fin 3 → ℝ := ![![(775193661152603/67500000000:ℝ), (156586072664273/11250000000:ℝ), (35095918420531/13500000000:ℝ)],
![(134395935407287/6750000000:ℝ), (23656437308033/1125000000:ℝ), (9857117117417/6750000000:ℝ)],
![(647211382563167/67500000000:ℝ), (35289400412429/3750000000:ℝ), (0:ℝ)]]
theorem row241_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (2120384426715569/100663296000000000:ℝ) row241_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row241_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row241_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row241_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row241_coefficients]

def row242_coefficients : Fin 3 → Fin 3 → ℝ := ![![(653444869372873/22500000000:ℝ), (1371777356338291/33750000000:ℝ), (88264102425287/7500000000:ℝ)],
![(1455558582056339/33750000000:ℝ), (844436633989519/16875000000:ℝ), (27209647700581/3750000000:ℝ)],
![(1258416239707999/67500000000:ℝ), (623207032284277/33750000000:ℝ), (0:ℝ)]]
theorem row242_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (13716424098201127/671088640000000000:ℝ) row242_coefficients
      (33/64:ℝ) (69/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row242_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row242_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row242_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row242_coefficients]

def row243_coefficients : Fin 3 → Fin 3 → ℝ := ![![(1131666728261599/13500000000:ℝ), (1501177590762193/11250000000:ℝ), (3359888720534783/67500000000:ℝ)],
![(3460373271218579/33750000000:ℝ), (753757887283333/5625000000:ℝ), (1073746195863949/33750000000:ℝ)],
![(2480825953997663/67500000000:ℝ), (411470629809703/11250000000:ℝ), (0:ℝ)]]
theorem row243_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (162116263224415861/8053063680000000000:ℝ) row243_coefficients
      (33/64:ℝ) (69/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row243_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row243_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row243_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row243_coefficients]

def row244_coefficients : Fin 3 → Fin 3 → ℝ := ![![(161575286784821/1875000000:ℝ), (7301666050784/52734375:ℝ), (13830386867264/263671875:ℝ)],
![(1765283899791361/16875000000:ℝ), (12203335070816/87890625:ℝ), (9117851648384/263671875:ℝ)],
![(2456821603718773/67500000000:ℝ), (9550075892888/263671875:ℝ), (0:ℝ)]]
theorem row244_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (3248279655369/163840000000000:ℝ) row244_coefficients
      (33/64:ℝ) (69/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row244_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row244_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row244_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row244_coefficients]

def row245_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4235570231360358793937/172503252857109375000:ℝ), (6860934571433130110299/172503252857109375000:ℝ), (1386587408854666908181/86251626428554687500:ℝ), (0:ℝ)],
![(5695682319484875771089/86251626428554687500:ℝ), (9358375248820502244787/86251626428554687500:ℝ), (4004200188965539197107/86251626428554687500:ℝ), (186362001975188921/118314988242187500:ℝ)],
![(8791380805069392748241/172503252857109375000:ℝ), (633855688020133024363/6900130114284375000:ℝ), (8522895873693741248627/172503252857109375000:ℝ), (1621074937311122617/236629976484375000:ℝ)]]
theorem row245_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1874083989640844075311/73518374584320000000000:ℝ) row245_coefficients
      (69/128:ℝ) (3/4:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row245_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row245_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row245_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row245_coefficients]

def row246_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5116366349949211390199/9583514047617187500:ℝ), (9802749414428966537873/9583514047617187500:ℝ), (782432459613631066279/1597252341269531250:ℝ), (0:ℝ)],
![(6746661143228164071107/4791757023808593750:ℝ), (13046730448392890159561/4791757023808593750:ℝ), (2146442330057002926467/1597252341269531250:ℝ), (14203635616809187883/532417447089843750:ℝ)],
![(3859505980309382408743/1916702809523437500:ℝ), (47937379733052103960649/9583514047617187500:ℝ), (12921377847267298182851/3194504682539062500:ℝ), (1123154234175189181291/1064834894179687500:ℝ)]]
theorem row246_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (17372641525740917513533/882220495011840000000000:ℝ) row246_coefficients
      (69/128:ℝ) (3/4:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row246_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row246_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row246_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row246_coefficients]

def row247_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5527232313675984987866/2395878511904296875:ℝ), (440263043827635872812/88736241181640625:ℝ), (591942990015766323161/191670280952343750:ℝ), (25613940301886114789/59157494121093750:ℝ)],
![(2313159101911420147904/479175702380859375:ℝ), (501905086036377351232/53241744708984375:ℝ), (2205129168861476013184/479175702380859375:ℝ), (0:ℝ)],
![(25744008528829390251104/2395878511904296875:ℝ), (7643672929712931566624/266208723544921875:ℝ), (12144245126886761765024/479175702380859375:ℝ), (218125974014405123168/29578747060546875:ℝ)]]
theorem row247_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (12174187807419104183/735183745843200000000:ℝ) row247_coefficients
      (69/128:ℝ) (3/4:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row247_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row247_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row247_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row247_coefficients]

def row248_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29818627404517390649876/2395878511904296875:ℝ), (72307107699480507579032/2395878511904296875:ℝ), (18519858514890396691987/798626170634765625:ℝ), (290423162809057007429/53241744708984375:ℝ)],
![(8607884298682515783296/479175702380859375:ℝ), (17003136220601643297152/479175702380859375:ℝ), (2798798139454875837952/159725234126953125:ℝ), (0:ℝ)],
![(162865341908040809271104/2395878511904296875:ℝ), (457729569928388972232128/2395878511904296875:ℝ), (142524515900251313136448/798626170634765625:ℝ), (2949007683993906143296/53241744708984375:ℝ)]]
theorem row248_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (663202172361689096423/44111024750592000000000:ℝ) row248_coefficients
      (69/128:ℝ) (3/4:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row248_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row248_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row248_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row248_coefficients]

def row249_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7498696084666344258632/95835140476171875:ℝ), (165664137362727281035072/798626170634765625:ℝ), (432372785005109513673082/2395878511904296875:ℝ), (505537951071134852762/9859582353515625:ℝ)],
![(33166025402159233516544/479175702380859375:ℝ), (21970832844339730164736/159725234126953125:ℝ), (32747615627305456977664/479175702380859375:ℝ), (0:ℝ)],
![(228911565948640859075584/479175702380859375:ℝ), (1105281149261102148625408/798626170634765625:ℝ), (3199410430069116851135488/2395878511904296875:ℝ), (4230949951145410290688/9859582353515625:ℝ)]]
theorem row249_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (35045193093327387219/2450612486144000000000:ℝ) row249_coefficients
      (69/128:ℝ) (3/4:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row249_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row249_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row249_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row249_coefficients]

def row250_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1308158453004413090851568/2395878511904296875:ℝ), (3669132884316230448516368/2395878511904296875:ℝ), (379484269604095763480348/266208723544921875:ℝ), (117153549133527111760648/266208723544921875:ℝ)],
![(130157070448850774832896/479175702380859375:ℝ), (259480748837330496588032/479175702380859375:ℝ), (14369424542769469083904/53241744708984375:ℝ), (0:ℝ)],
![(8550359381148804542179712/2395878511904296875:ℝ), (25190886480709962629643392/2395878511904296875:ℝ), (916054260075320937917824/88736241181640625:ℝ), (899214883174647470701952/266208723544921875:ℝ)]]
theorem row250_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (19677605165315751698953/1411552792018944000000000:ℝ) row250_coefficients
      (69/128:ℝ) (3/4:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row250_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row250_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row250_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row250_coefficients]

def row251_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1375619082986470677539272/2395878511904296875:ℝ), (258309643275185478588812/159725234126953125:ℝ), (3623993907343891048454144/2395878511904296875:ℝ), (124996254253253226594304/266208723544921875:ℝ)],
![(128494856313890668677376/479175702380859375:ℝ), (85386582685582261425664/159725234126953125:ℝ), (127666034239301615599616/479175702380859375:ℝ), (0:ℝ)],
![(8414171089356553908011008/2395878511904296875:ℝ), (1652523339450098540613632/159725234126953125:ℝ), (24335945197791408185409536/2395878511904296875:ℝ), (884695802388422664912896/266208723544921875:ℝ)]]
theorem row251_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (260086698850363719/19145410048000000000:ℝ) row251_coefficients
      (69/128:ℝ) (3/4:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row251_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row251_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row251_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row251_coefficients]

def row252_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60546972316977279953637590420130593/5646699705280702095000000000000000:ℝ), (166282528716226756047639533346791779/5646699705280702095000000000000000:ℝ), (150924140481521672234366295433191779/5646699705280702095000000000000000:ℝ), (5020953786919132904484928056281177/627411078364522455000000000000000:ℝ)],
![(11163148843732470186103330319010593/2823349852640351047500000000000000:ℝ), (30838156321524503077477252165155619/2823349852640351047500000000000000:ℝ), (28795623866795279568486214620823979/2823349852640351047500000000000000:ℝ), (1013401821000360741901365863853217/313705539182261227500000000000000:ℝ)],
![(15318404057593576578569070217890593/5646699705280702095000000000000000:ℝ), (4493014040042422094263299052219919/1129339941056140419000000000000000:ℝ), (3941648834939932477479454202854501/2823349852640351047500000000000000:ℝ), (0:ℝ)]]
theorem row252_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
    Record12518109.Bernstein.bsum 2 3 (4413155266252792398308312888669407/1353679421619665633280000000000000000:ℝ) row252_coefficients
      (0:ℝ) (9/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newTop_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row252_coefficients, Fin.sum_univ_succ, power_newTop_old] <;> ring
theorem row252_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
  rw [row252_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row252_coefficients]

def row253_coefficients : Fin 3 → Fin 4 → ℝ := ![![(555837703347278697355057792037807923/313705539182261227500000000000000:ℝ), (1636796333572425924438626900286223769/313705539182261227500000000000000:ℝ), (1606079557103015756812080424459023769/313705539182261227500000000000000:ℝ), (175040308959289509909503772070202641/104568513060753742500000000000000:ℝ)],
![(123022091028051303796033075255588243/156852769591130613750000000000000:ℝ), (366198723684582832313800553173190489/156852769591130613750000000000000:ℝ), (363534093536659647896782447662131089/156852769591130613750000000000000:ℝ), (40119153626709373126338323248176281/52284256530376871250000000000000:ℝ)],
![(13574694360012343670685561959440807/313705539182261227500000000000000:ℝ), (24957487740277301102138869066904417/313705539182261227500000000000000:ℝ), (1142371735400169804602061173871361/31370553918226122750000000000000:ℝ), (0:ℝ)]]
theorem row253_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
    Record12518109.Bernstein.bsum 2 3 (39383168835021165109014192704592077/16244153059435987599360000000000000000:ℝ) row253_coefficients
      (0:ℝ) (9/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newTop_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row253_coefficients, Fin.sum_univ_succ, power_newTop_old] <;> ring
theorem row253_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
  rw [row253_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row253_coefficients]

def row254_coefficients : Fin 3 → Fin 4 → ℝ := ![![(424248310234814396060654499009201343/31370553918226122750000000000000:ℝ), (1260458220116679121131344906696724029/31370553918226122750000000000000:ℝ), (1248171509528915054080726316365844029/31370553918226122750000000000000:ℝ), (5085945674654942333457233440473103/387290789113902750000000000000:ℝ)],
![(100437537436622067781057421836338079/15685276959113061375000000000000:ℝ), (300327927951356087439277250137596413/15685276959113061375000000000000:ℝ), (299383827443175550466838348182681557/15685276959113061375000000000000:ℝ), (1228314036153599145785413825696583/193645394556951375000000000000:ℝ)],
![(17726595783601931160740589413813/133947711008651250000000000000:ℝ), (39426096279790188075640467133297849/156852769591130613750000000000000:ℝ), (9344357302030348496848444622673913/78426384795565306875000000000000:ℝ), (0:ℝ)]]
theorem row254_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
    Record12518109.Bernstein.bsum 2 3 (9118322111832453269788636040986219/4331774149182930026496000000000000000:ℝ) row254_coefficients
      (0:ℝ) (9/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newTop_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row254_coefficients, Fin.sum_univ_succ, power_newTop_old] <;> ring
theorem row254_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
  rw [row254_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row254_coefficients]

def row255_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1654914197214178673050701417914466563/15685276959113061375000000000000:ℝ), (4940169170467007885050867073081639689/15685276959113061375000000000000:ℝ), (4915595749291479750949629892419879689/15685276959113061375000000000000:ℝ), (543446925346216846316488079084235521/5228425653037687125000000000000:ℝ)],
![(405041546339743480245031862726874083/7842638479556530687500000000000:ℝ), (1213317605703528524653130011103798473/7842638479556530687500000000000:ℝ), (242310231247631237500524109488695533/1568527695911306137500000000000:ℝ), (5377001291658281907926965320887377/104568513060753742500000000000:ℝ)],
![(7067798625977357010557783201181191/15685276959113061375000000000000:ℝ), (68639550181538961170972969527022213/78426384795565306875000000000000:ℝ), (16655394022543180635912939839464379/39213192397782653437500000000000:ℝ), (0:ℝ)]]
theorem row255_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
    Record12518109.Bernstein.bsum 2 3 (102352066716012082226905849290653437/51981289790195160317952000000000000000:ℝ) row255_coefficients
      (0:ℝ) (9/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newTop_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row255_coefficients, Fin.sum_univ_succ, power_newTop_old] <;> ring
theorem row255_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .old δ p := by
  rw [row255_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row255_coefficients]

end
end Qrh.JointDetector.FineReturn.FinalEdges
