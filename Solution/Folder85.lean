module

public import Grothendieck.Folder85

@[expose] public section

/-!
# Folder 85: the fifth power of a `2 × 2` matrix

The proof of the trusted statement of `Challenge.Folder85`, by `Grothendieck.Folder85.pow_five_eq`.
-/

namespace Challenge.Folder85

theorem pow_five_eq {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) :
    g ^ 5 = (g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2) • g
      + (-(g.det) * (g.trace ^ 3 - 2 * g.det * g.trace)) • (1 : Matrix (Fin 2) (Fin 2) R) :=
  @Grothendieck.Folder85.pow_five_eq _ _ g

end Challenge.Folder85
