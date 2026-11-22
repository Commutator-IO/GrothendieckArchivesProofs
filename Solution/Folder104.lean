module

public import Grothendieck.Folder104

@[expose] public section

/-!
# Folder 104, page 4: the globular complex

The proof of the trusted statement of `Challenge.Folder104`, by
`Grothendieck.Folder104.globulaire_complexe`.
-/

namespace Challenge.Folder104

theorem globulaire_complexe {F₂ F₁ F₀ : Type*} (s₂ t₂ : F₂ → F₁) (s₁ t₁ : F₁ → F₀)
    (hs : s₁ ∘ s₂ = s₁ ∘ t₂) (ht : t₁ ∘ s₂ = t₁ ∘ t₂) :
    (Finsupp.lmapDomain ℤ ℤ t₁ - Finsupp.lmapDomain ℤ ℤ s₁) ∘ₗ
      (Finsupp.lmapDomain ℤ ℤ t₂ - Finsupp.lmapDomain ℤ ℤ s₂) = 0 :=
  @Grothendieck.Folder104.globulaire_complexe _ _ _ s₂ t₂ s₁ t₁ hs ht

end Challenge.Folder104
