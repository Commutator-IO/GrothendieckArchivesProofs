module

public import Grothendieck.RingTheory.Folder100

@[expose] public section

/-!
# Folder 100, page 38: points of dimension one avoiding countably many closed sets

The proof of the trusted statement of `Challenge.Folder100`, by
`Grothendieck.Folder100.Baire.exists_coheight_eq_one`.
-/

open IsLocalRing

namespace Challenge.Folder100

theorem exists_coheight_eq_one {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsDomain R] (hR : ¬ IsField R) {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i)) (hZu : ∀ i, Z i ≠ Set.univ) :
    ∃ x : PrimeSpectrum R, Order.coheight x = 1 ∧ ∀ i, x ∉ Z i :=
  @Grothendieck.Folder100.Baire.exists_coheight_eq_one _ _ _ _ _ _ hR _ _ Z hZ hZu

end Challenge.Folder100
