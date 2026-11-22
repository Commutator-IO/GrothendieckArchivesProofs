module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-!
# Folder 39, pages 18–19: the formal preparation theorem

The trusted statements of `Grothendieck.Folder39.preparation_adique` and
`Grothendieck.Folder39.preparation_discrete`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder39` proves exactly these
statements, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open PowerSeries Polynomial

namespace Challenge.Folder39

/-- *Adic case. `A` complete and separated for the `I`-adic topology, `aᵢ ∈ I` for `i < N`,
`a_N` a unit: `F` is regular, and every `G` is uniquely `QF + r` with `deg r < N`.* -/
theorem preparation_adique
    {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, coeff i F ∈ I) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  sorry

/-- *Discrete case. Over any commutative ring, if `a₀, …, a_{N-1}` are nilpotent and `a_N` is a
unit, `F` is regular and every `G` is uniquely `QF + r` with `deg r < N`.* -/
theorem preparation_discrete {A : Type*} [CommRing A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, IsNilpotent (coeff i F)) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  sorry

end Challenge.Folder39
