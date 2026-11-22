module

public import Grothendieck.Topology.Folder42

@[expose] public section

/-!
# Folder 42, page 3: the topological step of Lemme 1

The proof of the trusted statement of `Challenge.Folder42`, by
`Grothendieck.Folder42.isOpen_of_stableUnderGeneralization`.
-/

open TopologicalSpace

namespace Challenge.Folder42

theorem isOpen_of_stableUnderGeneralization
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    {E : Set X} (hgen : StableUnderGeneralization E)
    (hloc : ∀ x ∈ E, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ∩ closure {x} ⊆ E) : IsOpen E :=
  @Grothendieck.Folder42.isOpen_of_stableUnderGeneralization _ _ _ _ _ hgen hloc

end Challenge.Folder42
