module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

/-!
# Folder 125: the chain of equivalences of feuillet 2, and the lemma of feuillet 3

The trusted statements of `Grothendieck.Folder125.etage1_iff_etage2` and
`Grothendieck.Folder125.lemme_III18`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder125` proves exactly these
statements, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder125

/-- *Feuillet 2, premier étage ⇔ deuxième étage. In a long exact sequence
`⋯ → L p → G p → C p → L (p+1) → ⋯`, the terms `C p` vanish for all `p ≥ m` if and only if
`L p → G p` is bijective for `p > m` and surjective for `p = m`.* -/
theorem etage1_iff_etage2 {L G C : ℕ → Type*} [∀ p, AddCommGroup (L p)] [∀ p, AddCommGroup (G p)]
    [∀ p, AddCommGroup (C p)]
    (a : ∀ p, L p →+ G p) (b : ∀ p, G p →+ C p) (δ : ∀ p, C p →+ L (p + 1))
    (exG : ∀ p, Function.Exact (a p) (b p))
    (exC : ∀ p, Function.Exact (b p) (δ p))
    (exL : ∀ p, Function.Exact (δ p) (a (p + 1))) (m : ℕ) :
    (∀ p, m ≤ p → ∀ c : C p, c = 0) ↔
      (∀ p, m < p → Function.Bijective (a p)) ∧ Function.Surjective (a m) := by
  sorry

/-- *Feuillet 3 (III-18), affine form. `R` noetherian, `B` a finite `R`-module, `u : Rⁿ → B` an
isomorphism on the germs at `𝔭`: then `u` is an isomorphism over a neighbourhood `D(f)`
of `𝔭`.* -/
theorem lemme_III18 {R : Type*} [CommRing R] [IsNoetherianRing R] {B : Type*} [AddCommGroup B]
    [Module R B] [Module.Finite R B] {n : ℕ} (u : (Fin n → R) →ₗ[R] B) (p : Ideal R) [p.IsPrime]
    (hu : Function.Bijective (LocalizedModule.map p.primeCompl u)) :
    ∃ f : R, f ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) := by
  sorry

end Challenge.Folder125
