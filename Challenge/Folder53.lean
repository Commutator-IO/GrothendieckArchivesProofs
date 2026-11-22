module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Sober

@[expose] public section

/-!
# Folder 53, page 9: the Galois argument, in topological form

The trusted statement of `Grothendieck.Folder53.irreducibleSpace_of_stable`, written with Mathlib
alone and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder53`
proves exactly this statement, through the untrusted imports of this repository, with no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open scoped Pointwise

namespace Challenge.Folder53

/-- *Let `p : X' → X` be closed and generalizing with `X` irreducible, `X'` and `X` sober, and a
group `G` acting on `X'` by homeomorphisms, transitively on the fibres of `p`. If an
irreducible `G`-stable set `S` contains a point through which only one irreducible
component of `X'` passes, then `X'` is irreducible.* -/
theorem irreducibleSpace_of_stable
    {X' : Type*} {X : Type*} {G : Type*} [TopologicalSpace X'] [TopologicalSpace X]
    [Group G] [MulAction G X'] [ContinuousConstSMul G X']
    [QuasiSober X'] [QuasiSober X] [IrreducibleSpace X]
    (p : X' → X) (hpc : IsClosedMap p) (hpg : GeneralizingMap p)
    (horb : ∀ x y, p x = p y → ∃ g : G, g • x = y)
    {S : Set X'} (hS : IsIrreducible S) (hSG : ∀ g : G, g • S ⊆ S) {s : X'} (hs : s ∈ S)
    (huniq : ∀ C ∈ irreducibleComponents X', ∀ D ∈ irreducibleComponents X',
      s ∈ C → s ∈ D → C = D) :
    IrreducibleSpace X' := by
  sorry

end Challenge.Folder53
