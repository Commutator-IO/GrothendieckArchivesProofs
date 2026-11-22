module

public meta import Lean

/-!
# The `mmp` tag attribute

Links a declaration to the label of the item (definition, lemma or theorem) of the minimal
model program, or of the background it uses, that the declaration formalizes. It is written as
the attribute name followed by the label as a string literal, on the line above the
declaration; an optional second string names one part of an enumerated statement. A
declaration may carry several labels, and a label may be carried by several declarations. The
attribute has no effect on elaboration.

The syntax is deliberately not written out literally in this docstring, so that tools scanning
the sources for tags do not mistake an example for a real one.

## Reading the registrations

Every application adds the pair (declaration, label) to the persistent environment extension
`MMP.mmpTagExt`, so the registrations are stored in the `.olean` files and can be read from an
imported environment. `MMP.mmpTags` returns them all, imported ones first; the command
`#mmp_tags` prints them, one per line.
-/

public meta section

open Lean Elab Command

namespace MMP

/-- The registrations of the `mmp` attribute: (declaration, label), in
import order and then in the order of application. -/
initialize mmpTagExt : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

/-- Every (declaration, label) registration visible in `env`. -/
def mmpTags (env : Environment) : Array (Name × String) :=
  mmpTagExt.getState env

end MMP

/-- Links a Lean declaration to a label: the attribute name, then the label in quotes,
optionally followed by a part in quotes. Not written literally here — see the module
docstring. -/
syntax (name := mmp) "mmp " str (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name  := `mmp
  descr := "marks a declaration as formalizing an item of the minimal model program"
  applicationTime := .afterTypeChecking
  add   := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "the mmp attribute must be global"
    let label ← match stx with
      | `(attr| mmp $l:str $[$_part:str]?) => pure l.getString
      | _ => throwUnsupportedSyntax
    if label.isEmpty then
      throwError "the mmp attribute needs a non-empty label"
    modifyEnv (MMP.mmpTagExt.addEntry · (decl, label))
}

/-- Prints every `mmp` registration visible here, one `declaration ↦ label` per
line, imported ones first. -/
elab "#mmp_tags" : command => do
  let tags := MMP.mmpTags (← getEnv)
  if tags.isEmpty then
    logInfo "no mmp registrations"
  else
    logInfo <| m!"{tags.size} mmp registration(s):\n" ++
      MessageData.joinSep (tags.toList.map fun (d, l) => m!"{d} ↦ {l}") "\n"

end
