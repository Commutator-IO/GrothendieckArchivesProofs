module

public import Grothendieck.Folder153

@[expose] public section

/-!
# Folder 153, page 7: the Pascal matrix and `k[[T]]⁺`

The proof of the trusted statements of `Challenge.Folder153`, by `Grothendieck.Folder153.pascal_det`
and `Grothendieck.Folder153.geom_not_finite_coaddition`.
-/

namespace Challenge.Folder153

theorem pascal_det (k : Type*) [CommRing k] (N : ℕ) :
    (Matrix.of fun p q : Fin N => (((p : ℕ) + q).choose p : k)).det = 1 :=
  @Grothendieck.Folder153.pascal_det k _ N

theorem geom_not_finite_coaddition (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ)
    (a b : Fin n → ℕ → k) :
    ¬ ∀ p q : ℕ, (if p = 0 ∧ q = 0 then 0 else ((p + q).choose p : k)) = ∑ i, a i p * b i q :=
  @Grothendieck.Folder153.geom_not_finite_coaddition k _ _ n a b

end Challenge.Folder153
