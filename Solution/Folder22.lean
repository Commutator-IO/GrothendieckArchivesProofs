module

public import Grothendieck.Folder22

@[expose] public section

/-!
# Folder 22: Lemme 3.3 and the obstruction of pages 22 and 24

The proof of the trusted statements of `Challenge.Folder22`, by `Grothendieck.Folder22.lemme3_3` and
`Grothendieck.Folder22.no_derivation`.
-/

open PowerSeries TensorProduct

namespace Challenge.Folder22

theorem lemme3_3 {A : Type*} [CommRing A] {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    Function.Bijective (TensorProduct.piRightHom A A M P) :=
  @Grothendieck.Folder22.lemme3_3 _ _ _ P _ _ M _ _ _

theorem no_derivation {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
    {R : Type*} [CommRing R] [Algebra R k] [Nontrivial k] {ι : Type*} (b : Module.Basis ι k M)
    (e : ℕ → ι) (he : Function.Injective e) (a : ℕ → k) (D : Derivation R k⟦X⟧ (k⟦X⟧ ⊗[k] M))
    (hD : ∀ n, D (C (a n)) = 1 ⊗ₜ b (e n)) : False :=
  @Grothendieck.Folder22.no_derivation _ _ _ _ _ _ _ _ _ _ b e he a D hD

end Challenge.Folder22
