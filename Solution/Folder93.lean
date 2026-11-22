module

public import Grothendieck.AlgebraicGeometry.Folder93

@[expose] public section

/-!
# Folder 93: Jacobson's formula in rank one

The proof of the trusted statement of `Challenge.Folder93`, by
`Grothendieck.Folder93.PCurvature.jacobson`.
-/

namespace Challenge.Folder93

theorem jacobson {A : Type*} [CommRing A] (D : Derivation ℤ A A) (p : ℕ) [hp : Fact p.Prime]
    [CharP A p] (a : A) :
    ((D : Module.End ℤ A) + LinearMap.mulLeft ℤ a) ^ p =
      (D : Module.End ℤ A) ^ p + LinearMap.mulLeft ℤ (a ^ p + D^[p - 1] a) :=
  @Grothendieck.Folder93.PCurvature.jacobson _ _ D p _ _ a

end Challenge.Folder93
