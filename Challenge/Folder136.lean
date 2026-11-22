module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-!
# Folder 136, pages 26–31: the binomial lemma behind the « ombres »

Théorème 1 of finding `136-shadow-full-faithfulness`.

The trusted statement of `Grothendieck.Folder136.binomial_shadow_existsUnique`, written with Mathlib
alone and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder136`
proves exactly this statement, through the untrusted imports of this repository, with no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder136

/-- *If `c_{l,k} ξ_k = c_{l,k−i} ξ_{k+l}` for `k ≥ N`, `l ≥ 0`, with `c_{a,b} = binom(a+b, a)`,
there is a unique `ξ` with `ξ_k = binom(k, i) ξ` for every `k ≥ N`.* -/
theorem binomial_shadow_existsUnique {A : Type*} [AddCommGroup A] (ξ : ℕ → A) (N i : ℕ)
    (h : ∀ k l, N ≤ k → (k + l).choose l • ξ k = (k + l - i).choose l • ξ (k + l)) :
    ∃! x : A, ∀ k, N ≤ k → ξ k = k.choose i • x := by
  sorry

end Challenge.Folder136
