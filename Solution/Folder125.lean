module

public import Grothendieck.AlgebraicGeometry.Folder125

@[expose] public section

/-!
# Folder 125: the chain of equivalences of feuillet 2, and the lemma of feuillet 3

The proof of the trusted statements of `Challenge.Folder125`, by
`Grothendieck.Folder125.etage1_iff_etage2` and `Grothendieck.Folder125.lemme_III18`.
-/

namespace Challenge.Folder125

theorem etage1_iff_etage2 {L G C : ℕ → Type*} [∀ p, AddCommGroup (L p)] [∀ p, AddCommGroup (G p)]
    [∀ p, AddCommGroup (C p)]
    (a : ∀ p, L p →+ G p) (b : ∀ p, G p →+ C p) (δ : ∀ p, C p →+ L (p + 1))
    (exG : ∀ p, Function.Exact (a p) (b p))
    (exC : ∀ p, Function.Exact (b p) (δ p))
    (exL : ∀ p, Function.Exact (δ p) (a (p + 1))) (m : ℕ) :
    (∀ p, m ≤ p → ∀ c : C p, c = 0) ↔
      (∀ p, m < p → Function.Bijective (a p)) ∧ Function.Surjective (a m) :=
  @Grothendieck.Folder125.etage1_iff_etage2 _ _ _ _ _ _ a b δ exG exC exL m

theorem lemme_III18 {R : Type*} [CommRing R] [IsNoetherianRing R] {B : Type*} [AddCommGroup B]
    [Module R B] [Module.Finite R B] {n : ℕ} (u : (Fin n → R) →ₗ[R] B) (p : Ideal R) [p.IsPrime]
    (hu : Function.Bijective (LocalizedModule.map p.primeCompl u)) :
    ∃ f : R, f ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) :=
  @Grothendieck.Folder125.lemme_III18 _ _ _ _ _ _ _ _ u p _ hu

end Challenge.Folder125
