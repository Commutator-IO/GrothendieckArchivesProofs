module

public import Mathlib.LinearAlgebra.Finsupp.Defs

@[expose] public section

/-!
# Folder 104, page 4: the globular complex

The trusted statement of `Grothendieck.Folder104.globulaire_complexe`, written with Mathlib alone
and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder104` proves
exactly this statement, through the untrusted imports of this repository, with no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder104

/-- *For sources and targets `sₙ, tₙ : Fₙ → Fₙ₋₁` satisfying the globular identities
`sₙ₋₁ sₙ = sₙ₋₁ tₙ` and `tₙ₋₁ sₙ = tₙ₋₁ tₙ`, the maps `tₙ − sₙ : ℤ[Fₙ] → ℤ[Fₙ₋₁]` compose
to zero.* -/
theorem globulaire_complexe {F₂ F₁ F₀ : Type*} (s₂ t₂ : F₂ → F₁) (s₁ t₁ : F₁ → F₀)
    (hs : s₁ ∘ s₂ = s₁ ∘ t₂) (ht : t₁ ∘ s₂ = t₁ ∘ t₂) :
    (Finsupp.lmapDomain ℤ ℤ t₁ - Finsupp.lmapDomain ℤ ℤ s₁) ∘ₗ
      (Finsupp.lmapDomain ℤ ℤ t₂ - Finsupp.lmapDomain ℤ ℤ s₂) = 0 := by
  sorry

end Challenge.Folder104
