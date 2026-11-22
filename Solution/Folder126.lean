module

public import Grothendieck.AlgebraicGeometry.Folder126Glue

@[expose] public section

/-!
# Folder 126, pages 17–23: the proof of the trusted statement

`Challenge.Folder126.radicial_etale_factorisation`, proved by the untrusted
`Grothendieck/AlgebraicGeometry/Folder126Glue.lean`, with the universal homeomorphism unfolded by
Stacks 04DF.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Challenge.Folder126

theorem radicial_etale_factorisation {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [UniversallyOpen f] (n : ℕ)
    (hn : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
      Nonempty ({q : Spec (.of K) ⟶ X // q ≫ f = p} ≃ Fin n)) :
    ∃ (E : Scheme.{u}) (g : X ⟶ E) (h : E ⟶ Y),
      IsIntegralHom g ∧ UniversallyInjective g ∧ Surjective g ∧ IsFinite h ∧ Etale h ∧
        g ≫ h = f ∧
      ∀ {E' : Scheme.{u}} (e : E' ⟶ Y), Etale e → ∀ v : X ⟶ E', v ≫ e = f →
        ∃! u : E ⟶ E', u ≫ e = h ∧ g ≫ u = v := by
  obtain ⟨E, g, h, hg, hh, he, hgh, huniv⟩ :=
    Grothendieck.Folder126Glue.radicial_etale_factorisation f (n := n) hn
  obtain ⟨hi, hui, hs⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective g).1 hg
  exact ⟨E, g, h, hi, hui, hs, hh, he, hgh, fun e he' v hv => @huniv _ e he' v hv⟩

end Challenge.Folder126
