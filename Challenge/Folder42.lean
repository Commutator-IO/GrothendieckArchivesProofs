module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

@[expose] public section

/-!
# Folder 42, page 3: the topological step of Lemme 1

The trusted statement of `Grothendieck.Folder42.isOpen_of_stableUnderGeneralization`, written with
Mathlib alone and left unproved. `lake comparator` (`comparator.json`) checks that
`Solution.Folder42` proves exactly this statement, through the untrusted imports of this repository,
with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open TopologicalSpace

namespace Challenge.Folder42

/-- *In a noetherian sober space, a set `E` stable under generisation that contains, with each
of its points `x`, a neighbourhood of `x` in `closure {x}`, is open.* -/
theorem isOpen_of_stableUnderGeneralization
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    {E : Set X} (hgen : StableUnderGeneralization E)
    (hloc : ∀ x ∈ E, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ∩ closure {x} ⊆ E) : IsOpen E := by
  sorry

end Challenge.Folder42
