module

public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

/-!
# Folder 55, page 13: the corollary of Lemme B

The trusted statement of `Grothendieck.Folder55.isNoetherianRing_of_tilde`, written with Mathlib
alone and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder55`
proves exactly this statement, through the untrusted imports of this repository, with no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder55

/-- *`Γ(X, 𝒪_X)` is noetherian. If increasing sequences in a class `C` are stationary (Lemme
B), and every finitely generated ideal `I` gives a member `Ĩ` of `C`, monotonically, with
`Γ(Ĩ) = I` (Lemme A and its Corollaire 1), then `A` is noetherian.* -/
theorem isNoetherianRing_of_tilde {A P : Type*} [CommRing A] [PartialOrder P] (C : P → Prop)
    (hB : ∀ s : ℕ → P, Monotone s → (∀ k, C (s k)) → ∃ k₀, ∀ k ≥ k₀, s k = s k₀)
    (tilde : Ideal A → P) (Γ : P → Ideal A)
    (htilde_mono : ∀ I J : Ideal A, I.FG → J.FG → I ≤ J → tilde I ≤ tilde J)
    (htilde_mem : ∀ I : Ideal A, I.FG → C (tilde I))
    (hΓ : ∀ I : Ideal A, I.FG → Γ (tilde I) = I) :
    IsNoetherianRing A := by
  sorry

end Challenge.Folder55
