module

public import Grothendieck.Folder39

@[expose] public section

/-!
# Folder 39, pages 18–19: the formal preparation theorem

The proof of the trusted statements of `Challenge.Folder39`, by
`Grothendieck.Folder39.preparation_adique` and `Grothendieck.Folder39.preparation_discrete`.
-/

open PowerSeries Polynomial

namespace Challenge.Folder39

theorem preparation_adique
    {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, coeff i F ∈ I) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 :=
  @Grothendieck.Folder39.preparation_adique _ _ I _ F N h1 h2

theorem preparation_discrete {A : Type*} [CommRing A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, IsNilpotent (coeff i F)) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 :=
  @Grothendieck.Folder39.preparation_discrete _ _ F N h1 h2

end Challenge.Folder39
