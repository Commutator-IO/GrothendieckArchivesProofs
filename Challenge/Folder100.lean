module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Folder 100, page 38: points of dimension one avoiding countably many closed sets

Finding `100-baire-dimension-one-points`.

The trusted statement of `Grothendieck.Folder100.Baire.exists_coheight_eq_one`, written with Mathlib
alone and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder100`
proves exactly this statement, through the untrusted imports of this repository, with no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open IsLocalRing

namespace Challenge.Folder100

/-- *Let `R` be a complete noetherian local domain which is not a field. Countably many proper
closed subsets of `Spec R` miss some point `x` with `dim closure {x} = 1`.* -/
theorem exists_coheight_eq_one {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsDomain R] (hR : ¬ IsField R) {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i)) (hZu : ∀ i, Z i ≠ Set.univ) :
    ∃ x : PrimeSpectrum R, Order.coheight x = 1 ∧ ∀ i, x ∉ Z i := by
  sorry

end Challenge.Folder100
