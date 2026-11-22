module

public import Grothendieck.AlgebraicGeometry.Folder55

@[expose] public section

/-!
# Folder 55, page 13: the corollary of Lemme B

The proof of the trusted statement of `Challenge.Folder55`, by
`Grothendieck.Folder55.isNoetherianRing_of_tilde`.
-/

namespace Challenge.Folder55

theorem isNoetherianRing_of_tilde {A P : Type*} [CommRing A] [PartialOrder P] (C : P → Prop)
    (hB : ∀ s : ℕ → P, Monotone s → (∀ k, C (s k)) → ∃ k₀, ∀ k ≥ k₀, s k = s k₀)
    (tilde : Ideal A → P) (Γ : P → Ideal A)
    (htilde_mono : ∀ I J : Ideal A, I.FG → J.FG → I ≤ J → tilde I ≤ tilde J)
    (htilde_mem : ∀ I : Ideal A, I.FG → C (tilde I))
    (hΓ : ∀ I : Ideal A, I.FG → Γ (tilde I) = I) :
    IsNoetherianRing A :=
  @Grothendieck.Folder55.isNoetherianRing_of_tilde _ _ _ _ C hB tilde Γ htilde_mono htilde_mem hΓ

end Challenge.Folder55
