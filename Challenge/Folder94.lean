module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

/-!
# Folder 94, page 7: constant fibre rank over a reduced local ring

Finding `94-rank-constructibility` (Remarque 5 bis).

The trusted statement of `Grothendieck.Folder94.free_of_finrank_eq_of_isReduced`, written with
Mathlib alone and left unproved. `lake comparator` (`comparator.json`) checks that
`Solution.Folder94` proves exactly this statement, through the untrusted imports of this repository,
with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open Module IsLocalRing TensorProduct

namespace Challenge.Folder94

/-- *Over a reduced local ring `B`, a finite module `P` whose fibre rank at every minimal prime
equals its rank at the closed point is free.* -/
theorem free_of_finrank_eq_of_isReduced {B P : Type*} [CommRing B] [IsLocalRing B] [IsReduced B]
    [AddCommGroup P] [Module B P] [Module.Finite B P]
    (h : ∀ 𝔮 : PrimeSpectrum B, 𝔮.asIdeal ∈ minimalPrimes B →
      finrank (Localization.AtPrime 𝔮.asIdeal) (Localization.AtPrime 𝔮.asIdeal ⊗[B] P) =
        finrank (ResidueField B) (ResidueField B ⊗[B] P)) :
    Module.Free B P := by
  sorry

end Challenge.Folder94
