import JanischLehericy
import Lean.Replay

/-! Recheck the transitive dependencies of the exported statements with Lean's
kernel, starting from the standard library's Init environment. Private names from
different source files may share the same short name in the elaborator.
Run with `lake env lean Replay.lean` after `lake build`. -/

open Lean

private partial def dependencyClosure (src base : Environment)
    (pending : List Name) (seen : Std.HashMap Name ConstantInfo := {}) :
    Except String (Std.HashMap Name ConstantInfo) := do
  match pending with
  | [] => return seen
  | n :: rest =>
    if seen.contains n || (base.toKernelEnv.find? n).isSome then return ← dependencyClosure src base rest seen
    let some decl := src.find? n | throw s!"Missing declaration {n}"
    let mutualNames := match decl with
      | .inductInfo info => info.all ++ info.ctors
      | .ctorInfo info => [info.induct]
      | .recInfo info => info.all
      | _ => []
    let deps := decl.getUsedConstantsAsSet.toList ++ mutualNames
    return ← dependencyClosure src base (deps ++ rest) (seen.insert n decl)

/-- Each call to Lean's replay API uses one elaborator name table. When two
files contain the same private short name, verify one declaration and its
dependencies first, then continue with a fresh table over the checked kernel. -/
private partial def checkRoots (src base : Environment) (roots : List Name) : IO Environment := do
  let .ok deps := dependencyClosure src base roots | throw (IO.userError "Missing dependency")
  let mut shortNames : Std.HashMap Name Name := {}
  for (n, _) in deps do
    let key := privateToUserName n
    if let some other := shortNames[key]? then
      let .ok before := dependencyClosure src base [n] | throw (IO.userError "Missing dependency")
      let first := if before.contains other then other else n
      let checked ← checkRoots src base [first]
      return ← checkRoots src (Environment.ofKernelEnv checked.toKernelEnv) roots
    shortNames := shortNames.insert key n
  return ← Environment.replay deps (Environment.ofKernelEnv base.toKernelEnv)

run_cmd do
  let src ← getEnv
  let base ← importModules #[{ module := `Init }] {} 0
  let roots := [`JanischLehericy.truncated_bound, `JanischLehericy.janisch_lehericy,
    `JanischLehericy.conjecture_one_four]
  let .ok deps := dependencyClosure src base roots | throwError "Could not collect dependencies"
  let checked ← checkRoots src base roots
  for n in roots do
    unless (checked.toKernelEnv.find? n).isSome do throwError "Kernel replay missed {n}"
  logInfo m!"Kernel replay checked {deps.size} declarations above Init and all three exported theorems."
