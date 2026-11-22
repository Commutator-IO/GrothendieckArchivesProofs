module

public import Grothendieck.Folder16

@[expose] public section

/-!
# Folder 16: the algebraic inverse of Lefschetz, and the pseudo-inverse

The proof of the trusted statements of `Challenge.Folder16`, by
`Grothendieck.Folder16.inverse_Lefschetz_algebrique` and
`Grothendieck.Folder16.pseudo_inverse_unique`.
-/

namespace Challenge.Folder16

theorem inverse_Lefschetz_algebrique
    {K : Type*} {V : Type*} {W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    (F : Subfield K) (𝒜V : Subring (Module.End K V))
    (𝒜WV : Set (W →ₗ[K] V)) (𝒜VW : Set (V →ₗ[K] W))
    (hsmul : ∀ c ∈ F, ∀ g ∈ 𝒜V, c • g ∈ 𝒜V)
    (hD : ∀ g ∈ 𝒜V, ∀ j, g.charpoly.coeff j ∈ F)
    (hcomp₁ : ∀ g ∈ 𝒜V, ∀ h ∈ 𝒜WV, g ∘ₗ h ∈ 𝒜WV)
    (hcomp₂ : ∀ h ∈ 𝒜WV, ∀ k ∈ 𝒜VW, h ∘ₗ k ∈ 𝒜V)
    {u : W →ₗ[K] V} (hu : u ∈ 𝒜WV) (hub : Function.Bijective u)
    {v : V →ₗ[K] W} (hv : v ∈ 𝒜VW) (hvb : Function.Bijective v) :
    ∃ v' ∈ 𝒜WV, v' ∘ₗ v = LinearMap.id ∧ v ∘ₗ v' = LinearMap.id :=
  @Grothendieck.Folder16.inverse_Lefschetz_algebrique _ _ _ _ _ _ _ _ _ F 𝒜V 𝒜WV 𝒜VW hsmul hD hcomp₁
    hcomp₂ _ hu hub _ hv hvb

theorem pseudo_inverse_unique {E : Type*} [Ring E] {L Λ Λ' : E} (h : Λ * L * Λ = Λ)
    (h' : Λ' * L * Λ' = Λ') (hl : Λ * L = Λ' * L) (hr : L * Λ = L * Λ') : Λ = Λ' :=
  @Grothendieck.Folder16.pseudo_inverse_unique _ _ _ _ _ h h' hl hr

end Challenge.Folder16
