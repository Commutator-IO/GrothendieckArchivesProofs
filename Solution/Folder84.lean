module

public import Grothendieck.RingTheory.Folder84

@[expose] public section

/-!
# Folder 84, page 64: the product of quadratic algebras

The proof of the trusted statement of `Challenge.Folder84`, by
`Grothendieck.Folder84.identity_page64`.
-/

namespace Challenge.Folder84

theorem identity_page64 {A : Type*} [CommRing A] (b₁ c₁ b₂ c₂ u₁ u₂ : A) :
    (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁) ^ 2 + b₁ * b₂ * (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁)
        + (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)
      = b₂ ^ 2 * (u₁ ^ 2 + b₁ * u₁ + c₁) + b₁ ^ 2 * (u₂ ^ 2 + b₂ * u₂ + c₂)
        + 4 * ((u₁ ^ 2 + b₁ * u₁ + c₁) * (u₂ ^ 2 + b₂ * u₂ + c₂)
          - c₁ * (u₂ ^ 2 + b₂ * u₂ + c₂) - c₂ * (u₁ ^ 2 + b₁ * u₁ + c₁)) :=
  @Grothendieck.Folder84.identity_page64 _ _ b₁ c₁ b₂ c₂ u₁ u₂

end Challenge.Folder84
