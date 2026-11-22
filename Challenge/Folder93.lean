module

public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

/-!
# Folder 93: Jacobson's formula in rank one

The trusted statement of `Grothendieck.Folder93.PCurvature.jacobson`, written with Mathlib alone and
left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder93` proves exactly
this statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder93

/-- *Statement 2. In characteristic `p`, for a derivation `D` of `A` and `a ∈ A`,
`(D + a)ᵖ = Dᵖ + aᵖ + D^{p−1}(a)` as operators on `A`.* -/
theorem jacobson {A : Type*} [CommRing A] (D : Derivation ℤ A A) (p : ℕ) [hp : Fact p.Prime]
    [CharP A p] (a : A) :
    ((D : Module.End ℤ A) + LinearMap.mulLeft ℤ a) ^ p =
      (D : Module.End ℤ A) ^ p + LinearMap.mulLeft ℤ (a ^ p + D^[p - 1] a) := by
  sorry

end Challenge.Folder93
