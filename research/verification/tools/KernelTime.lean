import Candidate.Main
open Lean

/-- Re-check one theorem or definition in the kernel under a fresh name and return the time in
microseconds (none if it is not a theorem/definition, or if the check fails). -/
def kernelTime (kenv : Kernel.Environment) (n : Name) : IO (Option Nat) := do
  let t0 ← IO.monoNanosNow
  let decl? : Option Declaration := match kenv.find? n with
    | some (.thmInfo t) => some (.thmDecl { t with name := `KT ++ n })
    | some (.defnInfo d) => some (.defnDecl { d with name := `KT ++ n })
    | _ => none
  match decl? with
  | none => return none
  | some d =>
    let r := Kernel.Environment.addDeclCore kenv (t0 - t0).toUSize 100000 d none
    let ok := match r with | .ok _ => true | .error _ => false
    let t1 ← IO.monoNanosNow
    return if ok then some ((t1 - t0) / 1000) else none

#eval show CoreM Unit from do
  let env ← getEnv
  let kenv := env.toKernelEnv
  let dir := "OUT_DIR/"
  let names := (← IO.FS.lines (dir ++ "kt_names.txt")).toList.map String.toName
  let nThreads := 3
  let chunks := (List.range nThreads).map fun k =>
    (names.zip (List.range names.length)).filter (fun (_, i) => i % nThreads == k) |>.map (·.1)
  let tasks ← chunks.mapIdxM fun k chunk => IO.asTask (prio := .dedicated) do
    let h ← IO.FS.Handle.mk (dir ++ s!"kt_out_{k}.tsv") .write
    for n in chunk do
      let r ← kernelTime kenv n
      match r with
      | some us => h.putStrLn s!"{us}\t{n}"
      | none => h.putStrLn s!"-1\t{n}"
      h.flush
  for t in tasks do
    match ← IO.wait t with
    | .ok _ => pure ()
    | .error e => IO.println s!"task error {e}"
  IO.println "done"
