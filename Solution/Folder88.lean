module

public import Grothendieck.Folder88

@[expose] public section

/-!
# Folder 88, page 14: the hyperbolic case of the trichotomy

The proof of the trusted statement of `Challenge.Folder88`, by
`Grothendieck.Folder88.hyperbolique_iff`.
-/

namespace Challenge.Folder88

theorem hyperbolique_iff (p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) :
    2 * (p + q) < p * q ↔ 9 ≤ p + q ∧ (p, q) ≠ (3, 6) ∧ (p, q) ≠ (6, 3) :=
  @Grothendieck.Folder88.hyperbolique_iff p q hp hq

end Challenge.Folder88
