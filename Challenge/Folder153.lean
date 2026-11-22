module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Folder 153, page 7: the Pascal matrix and `k[[T]]⁺`

The trusted statements of `Grothendieck.Folder153.pascal_det` and
`Grothendieck.Folder153.geom_not_finite_coaddition`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder153` proves exactly these
statements, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder153

/-- *The Pascal matrix `(binom(p + q, p))_{p, q < N}` has determinant `1`.* -/
theorem pascal_det (k : Type*) [CommRing k] (N : ℕ) :
    (Matrix.of fun p q : Fin N => (((p : ℕ) + q).choose p : k)).det = 1 := by
  sorry

/-- *Page 7: `k[[T]]⁺` does not satisfy 3a). The coefficients of `F(X + Y)` for
`F = ∑_{m ≥ 1} T^m` are not those of a finite sum `∑ᵢ aᵢ(X) bᵢ(Y)`.* -/
theorem geom_not_finite_coaddition (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ)
    (a b : Fin n → ℕ → k) :
    ¬ ∀ p q : ℕ, (if p = 0 ∧ q = 0 then 0 else ((p + q).choose p : k)) = ∑ i, a i p * b i q := by
  sorry

end Challenge.Folder153
