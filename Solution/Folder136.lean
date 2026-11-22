module

public import Grothendieck.RingTheory.Folder136

@[expose] public section

/-!
# Folder 136, pages 26–31: the binomial lemma behind the « ombres »

The proof of the trusted statement of `Challenge.Folder136`, by
`Grothendieck.Folder136.binomial_shadow_existsUnique`.
-/

namespace Challenge.Folder136

theorem binomial_shadow_existsUnique {A : Type*} [AddCommGroup A] (ξ : ℕ → A) (N i : ℕ)
    (h : ∀ k l, N ≤ k → (k + l).choose l • ξ k = (k + l - i).choose l • ξ (k + l)) :
    ∃! x : A, ∀ k, N ≤ k → ξ k = k.choose i • x :=
  @Grothendieck.Folder136.binomial_shadow_existsUnique _ _ ξ N i h

end Challenge.Folder136
