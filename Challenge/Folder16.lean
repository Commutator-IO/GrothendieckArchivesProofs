module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

/-!
# Folder 16: the algebraic inverse of Lefschetz, and the pseudo-inverse

Finding `16-algebraic-iso-suffices` (pages 47–48).

The trusted statements of `Grothendieck.Folder16.inverse_Lefschetz_algebrique` and
`Grothendieck.Folder16.pseudo_inverse_unique`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder16` proves exactly these
statements, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder16

/-- *Pages 47–48, « un isomorphisme algébrique quelconque ». With « algebraic » read as
membership in given sets of maps satisfying `D(X)`: if `u : W → V` is some algebraic
isomorphism and `v : V → W` is an algebraic isomorphism, then `v⁻¹` is algebraic.* -/
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
    ∃ v' ∈ 𝒜WV, v' ∘ₗ v = LinearMap.id ∧ v ∘ₗ v' = LinearMap.id := by
  sorry

/-- *Pages 14–15, « unique quand il existe ». A pseudo-inverse `Λ` of `L` with `ΛLΛ = Λ` is
determined by the two idempotents `ΛL` and `LΛ`.* -/
theorem pseudo_inverse_unique {E : Type*} [Ring E] {L Λ Λ' : E} (h : Λ * L * Λ = Λ)
    (h' : Λ' * L * Λ' = Λ') (hl : Λ * L = Λ' * L) (hr : L * Λ = L * Λ') : Λ = Λ' := by
  sorry

end Challenge.Folder16
