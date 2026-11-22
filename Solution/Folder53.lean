module

public import Grothendieck.AlgebraicGeometry.Folder53

@[expose] public section

/-!
# Folder 53, page 9: the Galois argument, in topological form

The proof of the trusted statement of `Challenge.Folder53`, by
`Grothendieck.Folder53.irreducibleSpace_of_stable`.
-/

open scoped Pointwise

namespace Challenge.Folder53

theorem irreducibleSpace_of_stable
    {X' : Type*} {X : Type*} {G : Type*} [TopologicalSpace X'] [TopologicalSpace X]
    [Group G] [MulAction G X'] [ContinuousConstSMul G X']
    [QuasiSober X'] [QuasiSober X] [IrreducibleSpace X]
    (p : X' → X) (hpc : IsClosedMap p) (hpg : GeneralizingMap p)
    (horb : ∀ x y, p x = p y → ∃ g : G, g • x = y)
    {S : Set X'} (hS : IsIrreducible S) (hSG : ∀ g : G, g • S ⊆ S) {s : X'} (hs : s ∈ S)
    (huniq : ∀ C ∈ irreducibleComponents X', ∀ D ∈ irreducibleComponents X',
      s ∈ C → s ∈ D → C = D) :
    IrreducibleSpace X' :=
  @Grothendieck.Folder53.irreducibleSpace_of_stable _ _ _ _ _ _ _ _ _ _ _ p hpc hpg horb _ hS hSG _
    hs huniq

end Challenge.Folder53
