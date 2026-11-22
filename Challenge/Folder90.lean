module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

/-!
# Folder 90, page 9: the components criterion

Finding `90-components-criterion`.

The trusted statement of `Grothendieck.Folder90.iInf_pow_eq_bot_iff`, written with Mathlib alone and
left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder90` proves exactly
this statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder90

/-- *For `A` reduced and noetherian, `⋂ₙ πⁿA = 0` if and only if every irreducible component
of `Spec A` meets the special fibre `V(π)`.* -/
theorem iInf_pow_eq_bot_iff {A : Type*} [CommRing A] (π : A) [IsNoetherianRing A] [IsReduced A] :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ ↔ ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤ := by
  sorry

end Challenge.Folder90
