module

public import Mathlib.Algebra.Ring.Defs

@[expose] public section

/-!
# Folder 84, page 64: the product of quadratic algebras

Finding `84-product-quadratic-algebras-formula`.

The trusted statement of `Grothendieck.Folder84.identity_page64`, written with Mathlib alone and
left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder84` proves exactly
this statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder84

/-- *With `Qᵢ = uᵢ² + bᵢuᵢ + cᵢ` and `u = u₁b₂ + u₂b₁ + 2u₁u₂`,
`u² + bu + c = b₂²Q₁ + b₁²Q₂ + 4(Q₁Q₂ − c₁Q₂ − c₂Q₁)` for `b = b₁b₂`,
`c = c₁b₂² + c₂b₁² − 4c₁c₂`.* -/
theorem identity_page64 {A : Type*} [CommRing A] (b₁ c₁ b₂ c₂ u₁ u₂ : A) :
    (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁) ^ 2 + b₁ * b₂ * (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁)
        + (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)
      = b₂ ^ 2 * (u₁ ^ 2 + b₁ * u₁ + c₁) + b₁ ^ 2 * (u₂ ^ 2 + b₂ * u₂ + c₂)
        + 4 * ((u₁ ^ 2 + b₁ * u₁ + c₁) * (u₂ ^ 2 + b₂ * u₂ + c₂)
          - c₁ * (u₂ ^ 2 + b₂ * u₂ + c₂) - c₂ * (u₁ ^ 2 + b₁ * u₁ + c₁)) := by
  sorry

end Challenge.Folder84
