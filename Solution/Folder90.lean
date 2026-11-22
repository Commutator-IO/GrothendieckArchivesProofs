module

public import Grothendieck.AlgebraicGeometry.Folder90

@[expose] public section

/-!
# Folder 90, page 9: the components criterion

The proof of the trusted statement of `Challenge.Folder90`, by
`Grothendieck.Folder90.iInf_pow_eq_bot_iff`.
-/

namespace Challenge.Folder90

theorem iInf_pow_eq_bot_iff {A : Type*} [CommRing A] (π : A) [IsNoetherianRing A] [IsReduced A] :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ ↔ ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤ :=
  @Grothendieck.Folder90.iInf_pow_eq_bot_iff _ _ π _ _

end Challenge.Folder90
