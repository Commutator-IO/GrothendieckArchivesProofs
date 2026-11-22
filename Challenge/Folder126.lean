module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-!
# Folder 126, pages 17–23: the trusted statement

The statement of `Grothendieck.Folder126Glue.radicial_etale_factorisation`, written with Mathlib
alone and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder126`
proves exactly this statement, through the untrusted imports of `Grothendieck/` and Stacks, with
no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

*Let `f : X ⟶ Y` be finite and universally open, and suppose every geometric fibre of `f` has
exactly `n` points. Then `f` factors as `X ⟶ E ⟶ Y` with `X ⟶ E` integral, universally injective
and surjective (a universal homeomorphism) and `E ⟶ Y` finite étale, and every `Y`-morphism from
`X` to an étale `Y`-scheme factors uniquely through `X ⟶ E`.*

The universal homeomorphism of the proof is a notion of AxiomMath/Stacks; here it is spelled
with Mathlib's integral, universally injective and surjective morphisms (Stacks 04DF).
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
  sorry

end Challenge.Folder126
