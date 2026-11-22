/-
Issue #31, question 4, in its affordable form: replay, through Lean's kernel, every constant of
this repository's own libraries, on top of an environment that holds only their dependencies
(Mathlib, Stacks and Lean, which are trusted as built). This catches a declaration that entered
the environment without being checked by the kernel (a metaprogram calling `addDecl` unchecked,
an `unsafe` trick, a corrupted `.olean`), in minutes; it does not use an independent kernel.

Usage: `lake env lean --run scripts/ReplayOwn.lean <root module> <library prefix>...`, e.g.
`lake env lean --run scripts/ReplayOwn.lean GrothendieckArchivesProofs Grothendieck Buffalo`.
-/
import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  let root :: prefixes := args | do
    IO.eprintln "usage: ReplayOwn <root module> <library prefix>..."
    return 2
  let prefixes := prefixes.map String.toName
  let isOwn (m : Name) : Bool := prefixes.any (·.isPrefixOf m)
  initSearchPath (← findSysroot)
  -- The full environment, to find the repository's modules and constants.
  let full ← importModules #[{ module := root.toName }] {} 0
  let mods := full.header.moduleNames
  let deps := mods.filter (fun m => !isOwn m)
  let own := mods.filter isOwn
  -- The environment of the dependencies alone: the repository's constants are not in it.
  let base ← importModules (deps.map fun m => { module := m }) {} 0
  let mut todo : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in full.constants.map₁.toList do
    match full.getModuleIdxFor? n with
    | some idx =>
      if isOwn mods[idx.toNat]! && !base.contains n then
        todo := todo.insert n ci
    | none => pure ()
  IO.println s!"{own.size} modules of the repository, {deps.size} dependencies; \
    replaying {todo.size} constants through the kernel"
  try
    discard <| Kernel.Environment.replay todo base.toKernelEnv
  catch e =>
    IO.eprintln s!"replay failed: {e}"
    return 1
  IO.println "All the repository's constants were accepted by the kernel."
  return 0
