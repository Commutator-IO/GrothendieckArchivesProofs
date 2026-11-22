import Lean

/-!
# What this repository re-proves

Issue #39, step 1b: find, by script and not by eye, the theorems of this repository that Mathlib
or AxiomMath/Stacks already has. Run after `lake build`:

    lake env lean --run scripts/FindDuplicates.lean <root module> <output file> <module prefix>...

Imports the root module (or several, separated by commas). The theorems declared in a module
whose name starts with one of the prefixes are *ours*; every other theorem of the environment
(Mathlib, the Stacks modules the root imports, Lean's core libraries) is a *library* theorem.
For a `def … : Prop` of ours (the open problems of `OpenProblems/`), its body is read as a
statement: a match there means that the « open » problem is a library theorem.

Two comparisons:

* **Same statement.** Two types are the same when they are equal (`==`, that is up to binder names
  and binder info, so instance-implicit and implicit binders compare as their types) after
  * the universe parameters are renamed in order of first occurrence,
  * metadata (`mdata`) and the type annotations `optParam`, `autoParam`, `outParam` are dropped.

  The comparison goes through a hash of the normalised type, then `==` on the bucket. Pairs of
  our own theorems with the same statement are listed too: they are near-duplicates to merge.
* **Same conclusion, weaker or equal hypotheses** (bonus). A library theorem `L` is a candidate
  for one of ours, `T`, when their conclusions have the same *skeleton* (the conclusion, each
  bound variable replaced by the skeleton of its type, instances erased, universes erased). Each
  candidate is then checked in `MetaM`, those with the fewest hypotheses first: with `T`'s
  hypotheses as local variables, `L`'s conclusion must unify with `T`'s, unfolding only reducible
  definitions and instances, and each hypothesis of `L` left over must be an instance found by
  synthesis or a local variable of the same type (same transparency). Then `T` is `L` applied to
  some of `T`'s own hypotheses: a one-line corollary. Skeleton buckets with more than `maxBucket`
  library theorems are too generic to check (`a = b`, `x ∈ s`) and are skipped, and so is every
  check that exceeds `heartbeats`. Set `FIND_DUPLICATES_DEBUG` to print the buckets.

The report (Markdown) gives the counts and three tables: our theorems with the same statement as a
library theorem, our theorems with the same statement as another of ours, and our theorems that are
a library theorem applied to some of their hypotheses. A theorem whose proof is already a constant
application of the library theorem it matches (an `alias`, or `L ..`) is marked « reuses ».
-/

open Lean Meta

/-- Lemmas the compiler generates (equation lemmas, `sizeOf` specs, congruence and injectivity
lemmas): their statements repeat those of the declarations they come from. -/
def isGenerated (n : Name) : Bool :=
  match n with
  | .str _ s =>
    ["sizeOf_spec", "congr_simp", "injEq", "inj", "ext_iff", "eq_def", "proof_1", "proof_2",
      "proof_3", "proof_4"].contains s ||
      (s.startsWith "eq_" && (s.drop 3).all Char.isDigit) || s.startsWith "match_" ||
      s.startsWith "_" || s.startsWith "proof_"
  | _ => true

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def hasPrefix (prefixes : List Name) (mod : Name) : Bool :=
  prefixes.any fun p => p.isPrefixOf mod

/-- The library a module belongs to, for the report. -/
def library (mod : Name) : String :=
  match mod.getRoot with
  | `StacksCore | `StacksFrontier | `Stacks => "Stacks"
  | `Mathlib => "Mathlib"
  | r => r.toString

/-- Whether `e` is `optParam α d`, `autoParam α stx` or `outParam α`; then `α`. -/
def annotated? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``optParam 2 || e.isAppOfArity ``autoParam 2 then some e.appFn!.appArg!
  else if e.isAppOfArity ``outParam 1 then some e.appArg!
  else none

/-- Drops metadata and the type annotations that do not change the statement. Uses the native
`Expr.replace`; the recursive call only happens at an annotation, which is rare. -/
partial def stripAnnotations (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripAnnotations b)
    | e@(.app ..) => (annotated? e).map stripAnnotations
    | _ => none

/-- The universe parameters of `e`, in order of first occurrence. -/
def levelParamsInOrder (e : Expr) : Array Name :=
  (CollectLevelParams.main e {}).params

/-- The normal form of a statement: universe parameters renamed `u_0, u_1, …` in order of first
occurrence, annotations dropped. -/
def normalise (e : Expr) : Expr :=
  let e := stripAnnotations e
  let ps := levelParamsInOrder e
  let canon := (List.range ps.size).map fun i => Level.param (Name.mkSimple s!"u_{i}")
  e.instantiateLevelParams ps.toList canon

/-- Whether `c` builds instances: an instance, or the projection of a class to a parent class
(`CommRing.toRing`). -/
def isInstanceLike (env : Environment) (c : Name) : Bool :=
  Meta.isInstanceCore env c ||
    match env.getProjectionFnInfo? c, env.find? c with
    | some info, some ci =>
      info.fromClass && match ci.type.getForallBody.getAppFn with
        | .const k _ => isClass env k
        | _ => false
    | _, _ => false

/-- The skeleton of a conclusion: each bound variable of the telescope replaced by (a marker
applied to) the skeleton of its type, each instance (an instance-implicit variable, or a term
headed by an instance) replaced by a marker, universes erased. Two statements with the same
conclusion and hypotheses in another order, more hypotheses, or other instance paths, have the
same skeleton. -/
def skeleton (env : Environment) (ty : Expr) : Expr := Id.run do
  let ty := stripAnnotations ty
  let ps := levelParamsInOrder ty
  let ty := ty.instantiateLevelParams ps.toList (ps.toList.map fun _ => Level.zero)
  let marker := mkConst `FindDuplicates.var
  let inst := mkConst `FindDuplicates.inst
  let eraseInst (e : Expr) : Expr := e.replace fun e =>
    match e.getAppFn with
    | .const c _ => if isInstanceLike env c then some inst else none
    | _ => none
  let mut subs : Array Expr := #[]
  let mut e := ty
  while e.isForall do
    let .forallE _ d b bi := e | break
    subs := subs.push <|
      if bi.isInstImplicit then inst else mkApp marker (eraseInst (d.instantiateRev subs))
    e := b
  return eraseInst (e.instantiateRev subs)

/-- The statement a constant of ours puts forward: a theorem's type, or the body of a
`def … : Prop`. -/
def statementOf? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo t => some t.type
  | .defnInfo d => if d.type.isProp then some d.value else none
  | _ => none

/-- Whether the proof of `ours` already calls `lib`: its value, under its lambdas, is an
application of `lib`. -/
def reuses (env : Environment) (ours lib : Name) : Bool :=
  match env.find? ours with
  | some (.thmInfo t) =>
    let rec body : Expr → Expr
      | .lam _ _ b _ => body b
      | .mdata _ b => body b
      | e => e
    (body t.value).getAppFn.constName? == some lib
  | _ => false

/-- Whether the library theorem `lib` proves the statement `stmt` once applied to some of its
hypotheses (see the module docstring). -/
def proves (lib : Name) (stmt : Expr) : MetaM Bool :=
  forallTelescope stmt fun xs concl => withTransparency .instances do
    let lc ← mkConstWithFreshMVarLevels lib
    let (mvs, bis, lconcl) ← forallMetaTelescope (← inferType lc)
    unless ← isDefEq lconcl concl do return false
    for mv in mvs, bi in bis do
      if ← mv.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← inferType mv)
      if bi.isInstImplicit then
        let some inst ← synthInstance? ty | return false
        unless ← isDefEq mv inst do return false
      else
        let mut found := false
        for x in xs do
          if ← isDefEq (← inferType x) ty then
            if ← isDefEq mv x then
              found := true
              break
        unless found do return false
    return true

def runMeta (env : Environment) (heartbeats : Nat) (act : MetaM Bool) : IO Bool := do
  let ctx : Core.Context := {
    fileName := "<FindDuplicates>", fileMap := default, maxHeartbeats := heartbeats * 1000
    initHeartbeats := ← IO.getNumHeartbeats }
  let st : Core.State := { env }
  match ← (act.run' {} {} |>.run ctx st |>.toBaseIO) with
  | .ok (b, _) => return b
  | .error e =>
    if (← IO.getEnv "FIND_DUPLICATES_DEBUG").isSome then
      IO.println s!"  error: {← e.toMessageData.toString}"
    return false

def maxBucket : Nat := 40
def heartbeats : Nat := 20000

def mdRow (cells : List String) : String := "| " ++ " | ".intercalate cells ++ " |\n"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | root :: out :: prefixStrs =>
    let prefixes := prefixStrs.map String.toName
    let debug := (← IO.getEnv "FIND_DUPLICATES_DEBUG").isSome
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let roots := (root.splitOn ",").toArray.map fun m => ({ module := m.toName } : Import)
    let env ← importModules roots {} (loadExts := true)
    -- Ours and the library's, by hash of the normalised statement and by skeleton hash.
    let mut ours : Array (Name × Name × Expr) := #[]
    let mut libByType : Std.HashMap UInt64 (Array (Name × Expr)) := {}
    let mut libBySkel : Std.HashMap UInt64 (Array Name) := {}
    let mut libCount := 0
    for (n, ci) in env.constants.map₁.toList do
      if n.isInternalDetail || isGenerated n then continue
      let some mod := moduleOf env n | continue
      if hasPrefix prefixes mod then
        if let some s := statementOf? ci then ours := ours.push (n, mod, s)
      else if let .thmInfo t := ci then
        libCount := libCount + 1
        let e := normalise t.type
        libByType := libByType.alter e.hash fun a? => some ((a?.getD #[]).push (n, e))
        let k := (skeleton env t.type).hash
        libBySkel := libBySkel.alter k fun a? => some ((a?.getD #[]).push n)
    ours := ours.qsort fun a b => a.1.toString < b.1.toString
    IO.println s!"{ours.size} statements of ours, {libCount} library theorems."
    -- Same statement.
    let mut exact : Array (Name × Name × Name) := #[]
    let mut oursByType : Std.HashMap UInt64 (Array (Name × Expr)) := {}
    let mut exactOurs : NameSet := {}
    for (n, mod, s) in ours do
      let e := normalise s
      for (l, le) in libByType.getD e.hash #[] do
        if le == e then
          exact := exact.push (n, mod, l)
          exactOurs := exactOurs.insert n
      oursByType := oursByType.alter e.hash fun a? => some ((a?.getD #[]).push (n, e))
    let mut internal : Array (Array Name) := #[]
    for (_, bucket) in oursByType.toList do
      if bucket.size < 2 then continue
      -- Split the bucket into classes of equal statements.
      let mut rest := bucket
      while h : 0 < rest.size do
        let e := rest[0].2
        let cls := rest.filter (·.2 == e)
        if cls.size > 1 then internal := internal.push (cls.map (·.1))
        rest := rest.filter (!·.2 == e)
    internal := internal.qsort fun a b => a[0]!.toString < b[0]!.toString
    IO.println s!"{exact.size} same-statement matches, {internal.size} internal classes."
    -- Same conclusion, weaker or equal hypotheses: theorems only (an open problem has no
    -- hypotheses to weaken).
    let mut weaker : Array (Name × Name × Name) := #[]
    let mut skipped := 0
    let mut checked := 0
    for (n, mod, s) in ours do
      if exactOurs.contains n then continue
      let some (.thmInfo _) := env.find? n | continue
      -- The candidates with the fewest hypotheses first: the most general statement.
      let arity (l : Name) : Nat := ((env.find? l).map (·.type.getForallBinderNames.length)).getD 0
      let cands := (libBySkel.getD (skeleton env s).hash #[]).qsort fun a b =>
        arity a < arity b || (arity a == arity b && a.toString < b.toString)
      if cands.isEmpty then continue
      if debug then IO.println s!"{n}: bucket {cands.size}"
      if cands.size > maxBucket then
        skipped := skipped + 1
        continue
      if debug then IO.println s!"{n}: {cands.size} candidates {cands.toList.take 5}"
      for l in cands do
        checked := checked + 1
        if ← runMeta env heartbeats (proves l s) then
          weaker := weaker.push (n, mod, l)
          break
    IO.println s!"{weaker.size} weaker-hypothesis matches ({checked} checks, {skipped} skipped)."
    -- Report.
    let mut md := "# What this repository re-proves\n\n"
    md := md ++ s!"Generated by `scripts/FindDuplicates.lean` from `{root}`, prefixes " ++
      s!"{", ".intercalate (prefixStrs.map (s!"`{·}`"))}. The library is every other theorem " ++
      "of the environment: Mathlib, the Stacks modules the root imports (not the whole of " ++
      "Stacks), and Lean's core libraries.\n\n"
    md := md ++ s!"- Statements of ours read (theorems, and `def … : Prop`): {ours.size}.\n"
    md := md ++ s!"- Library theorems: {libCount}.\n"
    md := md ++ s!"- Same statement as a library theorem: {exact.size}.\n"
    md := md ++ s!"- Classes of our own theorems with the same statement: {internal.size}.\n"
    md := md ++ s!"- A library theorem applied to some of their hypotheses: {weaker.size} " ++
      s!"({checked} candidates checked; {skipped} statements skipped, their conclusion being " ++
      s!"shared by more than {maxBucket} library theorems).\n\n"
    md := md ++ "## Same statement as a library theorem\n\n"
    md := md ++ mdRow ["Ours", "Module", "Library theorem", "Library", "Reuses"]
    md := md ++ "|---|---|---|---|---|\n"
    for (n, mod, l) in exact do
      let lib := ((moduleOf env l).map library).getD "core"
      md := md ++ mdRow [s!"`{n}`", s!"`{mod}`", s!"`{l}`", lib,
        if reuses env n l then "yes" else ""]
    md := md ++ "\n## Same statement as another theorem of ours\n\n"
    md := md ++ mdRow ["Theorems"] ++ "|---|\n"
    for cls in internal do
      md := md ++ mdRow [", ".intercalate (cls.toList.map (s!"`{·}`"))]
    md := md ++ "\n## A library theorem applied to some of their hypotheses\n\n"
    md := md ++ mdRow ["Ours", "Module", "Library theorem", "Library", "Reuses"]
    md := md ++ "|---|---|---|---|---|\n"
    for (n, mod, l) in weaker do
      let lib := ((moduleOf env l).map library).getD "core"
      md := md ++ mdRow [s!"`{n}`", s!"`{mod}`", s!"`{l}`", lib,
        if reuses env n l then "yes" else ""]
    IO.FS.writeFile out md
    IO.println s!"Report: {out}"
    return 0
  | _ =>
    IO.eprintln "usage: lake env lean --run scripts/FindDuplicates.lean <root module> <output> \
      <module prefix>..."
    return 2
