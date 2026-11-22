module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleDescentIntegral
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 126, pages 17–23: the radicial–étale factorisation, global universal property

Finding `126-radicial-etale-factorisation`, global form. The local core (over a strictly
henselian base) is `Grothendieck.Folder126RadicialEtale`. This file treats the part of the
statement that holds over any base scheme `Y`: *every `Y`-morphism from `X` to an étale
`Y`-scheme factors uniquely through `X^ét`*, and its consequence, *the factorisation is unique up
to unique isomorphism*. It uses neither the noetherian hypothesis nor the constancy of the
number of geometric points; those serve existence only.

**What is proved.** Let `g : X ⟶ Z` be integral, universally injective and surjective (for a
finite `g`: finite, surjective and radicial, the first arrow of page 17), and `h : Z ⟶ Y`
any morphism.
* `existsUnique_lift_of_integral`: for every étale `e : E ⟶ Y` and every `v : X ⟶ E` over `Y`
  (`v ≫ e = g ≫ h`), there is exactly one `u : Z ⟶ E` over `Y` with `g ≫ u = v`.
* `bijective_comp_of_integral`: the same as a bijection of `Y`-morphisms, `u ↦ g ≫ u`.
* `existsUnique_iso_of_factorisations`: two factorisations `X ⟶ Z ⟶ Y` and `X ⟶ Z' ⟶ Y`, each a
  universal homeomorphism followed by an étale morphism, are isomorphic by exactly one
  isomorphism `Z ≅ Z'` compatible with both arrows.

The proof is the topological invariance of the étale site, Stacks 0BTY, used in the form the
page needs. Existence of `u` is `Stacks.Etale.exists_section_of_universalHomeomorphism`, applied
to the section `(v, g)` of the étale base change `Z ×_Y E ⟶ Z` over `X`. Uniqueness is
`Stacks.Etale.hom_ext_of_surjective`: two `Y`-maps into an étale scheme agreeing after a
surjective map are equal, because the diagonal of an étale morphism is an open immersion.
Integral, universally injective and surjective is the same as universal homeomorphism (Stacks
04DF, `universalHomeomorphism_iff_integral_universallyInjective_surjective`).

**Existence.** The factorisation itself exists over any `Y`
(`Grothendieck.Folder126Glue.exists_radicial_etale_factorisation_of_hasGeomDegree`): by étale
descent from the splitting over étale neighbourhoods over a quasi-compact quasi-separated base
(`Grothendieck.Folder126Existence`), then by relative gluing over the affine opens, the
transitions coming from the uniqueness proved here; the noetherian hypothesis is not needed.
The full equivalence of étale sites
(Stacks 04DZ, `Stacks.Etale.etalePullback_isEquivalence`) is not needed here: full faithfulness,
which is what the universal property uses, suffices.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Grothendieck.Folder126RadicialEtaleGlobal

variable {X Z Y : Scheme.{u}}

/-- **Folder 126, page 23, universal property (universal homeomorphism form).** Let
`g : X ⟶ Z` be a universal homeomorphism and `h : Z ⟶ Y` any morphism. Every `Y`-morphism
`v : X ⟶ E` into an étale `Y`-scheme `E` factors uniquely as `g ≫ u` with `u : Z ⟶ E` a
`Y`-morphism. -/
@[montpellier "126, 23"]
theorem existsUnique_lift (g : X ⟶ Z) [UniversalHomeomorphism g] (h : Z ⟶ Y)
    {E : Scheme.{u}} (e : E ⟶ Y) [Etale e] (v : X ⟶ E) (hv : v ≫ e = g ≫ h) :
    ∃! u : Z ⟶ E, u ≫ e = h ∧ g ≫ u = v := by
  obtain ⟨t, ht₁, ht₂⟩ := Stacks.Etale.exists_section_of_universalHomeomorphism g
    (pullback.snd e h) (pullback.lift v g hv) (pullback.lift_snd _ _ _)
  refine ⟨t ≫ pullback.fst e h, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ht₁, Category.id_comp]
  · rw [← Category.assoc, ht₂, pullback.lift_fst]
  · rintro u' ⟨hu'₁, hu'₂⟩
    have hsurj : Surjective g := Stacks.Etale.surjective_of_universalHomeomorphism' g
    refine Stacks.Etale.hom_ext_of_surjective g hsurj.surj e u' _ ?_ ?_
    · rw [hu'₁, Category.assoc, pullback.condition, ← Category.assoc, ht₁, Category.id_comp]
    · rw [hu'₂, ← Category.assoc, ht₂, pullback.lift_fst]

/-- **Folder 126, page 23, universal property.** Let `g : X ⟶ Z` be integral, universally
injective and surjective (for a finite morphism: finite, surjective and radicial) and
`h : Z ⟶ Y` any morphism. Every `Y`-morphism `v : X ⟶ E` into an étale `Y`-scheme factors
uniquely through `g` by a `Y`-morphism. -/
@[montpellier "126, 23"]
theorem existsUnique_lift_of_integral (g : X ⟶ Z) [IsIntegralHom g] [UniversallyInjective g]
    [Surjective g] (h : Z ⟶ Y) {E : Scheme.{u}} (e : E ⟶ Y) [Etale e] (v : X ⟶ E)
    (hv : v ≫ e = g ≫ h) :
    ∃! u : Z ⟶ E, u ≫ e = h ∧ g ≫ u = v :=
  have : UniversalHomeomorphism g :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective g).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  existsUnique_lift g h e v hv

/-- The universal property as a bijection: for `g` integral, universally injective and
surjective, precomposition with `g` is a bijection from the `Y`-morphisms `Z ⟶ E` to the
`Y`-morphisms `X ⟶ E`, for every étale `Y`-scheme `E`. -/
@[montpellier "126, 17–23"]
theorem bijective_comp_of_integral (g : X ⟶ Z) [IsIntegralHom g] [UniversallyInjective g]
    [Surjective g] (h : Z ⟶ Y) {E : Scheme.{u}} (e : E ⟶ Y) [Etale e] :
    Function.Bijective (fun u : {u : Z ⟶ E // u ≫ e = h} =>
      (⟨g ≫ u.1, by rw [Category.assoc, u.2]⟩ : {v : X ⟶ E // v ≫ e = g ≫ h})) := by
  refine ⟨fun u₁ u₂ hu => ?_, fun v => ?_⟩
  · obtain ⟨_, -, huniq⟩ := existsUnique_lift_of_integral g h e (g ≫ u₁.1)
      (by rw [Category.assoc, u₁.2])
    exact Subtype.ext ((huniq _ ⟨u₁.2, rfl⟩).trans
      (huniq _ ⟨u₂.2, (congrArg Subtype.val hu).symm⟩).symm)
  · obtain ⟨u, ⟨hu₁, hu₂⟩, -⟩ := existsUnique_lift_of_integral g h e v.1 v.2
    exact ⟨⟨u, hu₁⟩, Subtype.ext hu₂⟩

/-- **Folder 126, uniqueness of the radicial–étale factorisation.** Two factorisations
`X ⟶ Z ⟶ Y` and `X ⟶ Z' ⟶ Y` of the same morphism, each a universal homeomorphism followed by
an étale morphism, are isomorphic by exactly one isomorphism `Z ≅ Z'` compatible with both
arrows. -/
@[montpellier "126, 17–23"]
theorem existsUnique_iso_of_factorisations {Z' : Scheme.{u}} (g : X ⟶ Z) (h : Z ⟶ Y)
    (g' : X ⟶ Z') (h' : Z' ⟶ Y) [UniversalHomeomorphism g] [UniversalHomeomorphism g']
    [Etale h] [Etale h'] (hgh : g ≫ h = g' ≫ h') :
    ∃! φ : Z ≅ Z', g ≫ φ.hom = g' ∧ φ.hom ≫ h' = h := by
  obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := existsUnique_lift g h h' g' hgh.symm
  obtain ⟨b, ⟨hb₁, hb₂⟩, -⟩ := existsUnique_lift g' h' h g hgh
  -- `a ≫ b` and `𝟙 Z` both lift `g` along `g`, and similarly on `Z'`.
  obtain ⟨_, -, hZ⟩ := existsUnique_lift g h h g rfl
  obtain ⟨_, -, hZ'⟩ := existsUnique_lift g' h' h' g' rfl
  have hab : a ≫ b = 𝟙 Z :=
    (hZ _ ⟨by rw [Category.assoc, hb₁, ha₁], by rw [← Category.assoc, ha₂, hb₂]⟩).trans
      (hZ _ ⟨Category.id_comp _, Category.comp_id _⟩).symm
  have hba : b ≫ a = 𝟙 Z' :=
    (hZ' _ ⟨by rw [Category.assoc, ha₁, hb₁], by rw [← Category.assoc, hb₂, ha₂]⟩).trans
      (hZ' _ ⟨Category.id_comp _, Category.comp_id _⟩).symm
  refine ⟨⟨a, b, hab, hba⟩, ⟨ha₂, ha₁⟩, fun φ ⟨hφ₁, hφ₂⟩ => ?_⟩
  obtain ⟨_, -, hlift⟩ := existsUnique_lift g h h' g' hgh.symm
  exact Iso.ext ((hlift _ ⟨hφ₂, hφ₁⟩).trans (hlift _ ⟨ha₁, ha₂⟩).symm)

end Grothendieck.Folder126RadicialEtaleGlobal
