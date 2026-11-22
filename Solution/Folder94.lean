module

public import Grothendieck.Folder94

@[expose] public section

/-!
# Folder 94, page 7: constant fibre rank over a reduced local ring

The proof of the trusted statement of `Challenge.Folder94`, by
`Grothendieck.Folder94.free_of_finrank_eq_of_isReduced`.
-/

open Module IsLocalRing TensorProduct

namespace Challenge.Folder94

theorem free_of_finrank_eq_of_isReduced {B P : Type*} [CommRing B] [IsLocalRing B] [IsReduced B]
    [AddCommGroup P] [Module B P] [Module.Finite B P]
    (h : ∀ 𝔮 : PrimeSpectrum B, 𝔮.asIdeal ∈ minimalPrimes B →
      finrank (Localization.AtPrime 𝔮.asIdeal) (Localization.AtPrime 𝔮.asIdeal ⊗[B] P) =
        finrank (ResidueField B) (ResidueField B ⊗[B] P)) :
    Module.Free B P :=
  @Grothendieck.Folder94.free_of_finrank_eq_of_isReduced _ _ _ _ _ _ _ _ h

end Challenge.Folder94
