module

public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

/-!
# Folder 77: the local step of Proposition 8.5

Finding `77-discriminant-extension-across-2`.

The trusted statement of `Grothendieck.Folder77.prop85_local`, written with Mathlib alone and left
unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder77` proves exactly this
statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open IsLocalRing

namespace Challenge.Folder77

/-- *`R` local with maximal ideal `2R`, `C` a nonzero finite unramified `R`-algebra without
`2`-torsion, `v ∈ C` with `v² = 4ⁿΔ`. Then `Δ = b² − 4c` in `R`.* -/
theorem prop85_local {R : Type*} {C : Type*} [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    [Algebra.FormallyUnramified R C] [Module.Finite R C] [Nontrivial C]
    (hm : maximalIdeal R = Ideal.span {2}) (h2C : ∀ x : C, 2 * x = 0 → x = 0)
    {Δ : R} {v : C} {n : ℕ} (hv : v ^ 2 = 4 ^ n * algebraMap R C Δ) :
    ∃ b c : R, b ^ 2 - 4 * c = Δ := by
  sorry

end Challenge.Folder77
