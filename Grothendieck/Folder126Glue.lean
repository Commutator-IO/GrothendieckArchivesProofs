/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Grothendieck.Folder126Existence
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Grothendieck.Attr

/-!
# Folder 126, pages 17–23: the radicial–étale factorisation over any base

Finding `126-radicial-etale-factorisation`. Let `f : X ⟶ Y` be finite and universally open, with
exactly `n` geometric points in every geometric fibre. Then `f` factors as a universal
homeomorphism `X ⟶ X^ét` followed by a finite étale morphism `X^ét ⟶ Y`
(`exists_radicial_etale_factorisation_of_hasGeomDegree`), for an arbitrary scheme `Y`; together
with `Grothendieck.Folder126RadicialEtaleGlobal`, the factorisation is unique up to unique
isomorphism and has the universal property of page 23. This is the statement of pages 17–23,
without the noetherian hypothesis.

**The gluing.** Over every affine open `V` of `Y` the factorisation exists
(`Grothendieck.Folder126Existence`). For `V' ⊆ V` the uniqueness of the factorisation gives a
unique map `X^ét_{V'} ⟶ X^ét_V` compatible with everything, and identifies `X^ét_{V'}` with the
restriction of `X^ét_V` to `V'`; so the `X^ét_V` form a relative gluing datum over the directed
cover of `Y` by its affine opens (Stacks 01LH, Mathlib's
`Scheme.Cover.RelativeGluingData`). The glued scheme is finite étale over `Y` (both properties are
local on the target), the maps `X_V ⟶ X^ét_V` glue to `X ⟶ X^ét`, and that map is a universal
homeomorphism by the geometric-point criterion, since over `X^ét_V` it is `X_V ⟶ X^ét_V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Grothendieck.Folder126GeometricPoints Grothendieck.Folder126EtaleSplitting

universe u

namespace Grothendieck.Folder126Glue

variable {X Y : Scheme.{u}}

/-- The directed cover of `Y` by its affine opens. -/
local notation "𝒰Y" => Scheme.AffineZariskiSite.directedCover Y

/-- The transition map `X_{V'} ⟶ X_V` of the base changes of `f` to `V' ⊆ V`; it is the transition
map of the pulled-back cover. -/
abbrev resX (f : X ⟶ Y) {V' V : Y.AffineZariskiSite} (i : V' ⟶ V) :
    pullback f ((𝒰Y).f V') ⟶ pullback f ((𝒰Y).f V) :=
  pullback.map f ((𝒰Y).f V') f ((𝒰Y).f V) (𝟙 _) ((𝒰Y).trans i) (𝟙 _) (by simp)
    (by rw [Category.comp_id, Scheme.Cover.trans_map])

theorem resX_snd (f : X ⟶ Y) {V' V : Y.AffineZariskiSite} (i : V' ⟶ V) :
    resX f i ≫ pullback.snd f ((𝒰Y).f V) = pullback.snd f ((𝒰Y).f V') ≫ (𝒰Y).trans i :=
  pullback.lift_snd _ _ _

theorem resX_fst (f : X ⟶ Y) {V' V : Y.AffineZariskiSite} (i : V' ⟶ V) :
    resX f i ≫ pullback.fst f ((𝒰Y).f V) = pullback.fst f ((𝒰Y).f V') := by
  simp [resX]

theorem resX_id (f : X ⟶ Y) (V : Y.AffineZariskiSite) : resX f (𝟙 V) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [resX_fst, Category.id_comp]
  · rw [resX_snd, Scheme.Cover.trans_id, Category.comp_id, Category.id_comp]

theorem resX_comp (f : X ⟶ Y) {V'' V' V : Y.AffineZariskiSite} (i : V'' ⟶ V') (j : V' ⟶ V) :
    resX f (i ≫ j) = resX f i ≫ resX f j := by
  apply pullback.hom_ext
  · rw [resX_fst, Category.assoc, resX_fst, resX_fst]
  · rw [resX_snd, Category.assoc, resX_snd, ← Category.assoc, resX_snd, Category.assoc,
      Scheme.Cover.trans_comp]

/-- **Folder 126, pages 17–22: the radicial–étale factorisation exists over any base.** Let
`f : X ⟶ Y` be finite and universally open with exactly `n` geometric points in every geometric
fibre. Then `f` factors as a universal homeomorphism `X ⟶ X^ét` followed by a finite étale
morphism `X^ét ⟶ Y`. -/
@[montpellier "126, 17–23"]
theorem exists_radicial_etale_factorisation_of_hasGeomDegree (f : X ⟶ Y) [IsFinite f]
    [UniversallyOpen f] {n : ℕ} (hn : HasGeomDegree f n) :
    ∃ (E : Scheme.{u}) (g₀ : X ⟶ E) (h₀ : E ⟶ Y),
      UniversalHomeomorphism g₀ ∧ IsFinite h₀ ∧ Etale h₀ ∧ g₀ ≫ h₀ = f := by
  classical
  -- The factorisation over each affine open.
  have hV : ∀ V : Y.AffineZariskiSite, ∃ (Z : Scheme.{u}) (g : pullback f ((𝒰Y).f V) ⟶ Z)
      (h : Z ⟶ (𝒰Y).X V), UniversalHomeomorphism g ∧ IsFinite h ∧ Etale h ∧
        g ≫ h = pullback.snd f ((𝒰Y).f V) := fun V => by
    have : IsAffine ((𝒰Y).X V) := V.2
    exact Folder126Existence.exists_radicial_etale_factorisation (pullback.snd f ((𝒰Y).f V))
      (hn.pullback_snd _)
  choose Z g h hg hh hhe hgh using hV
  -- The transition maps, from the uniqueness of the factorisation.
  have hu : ∀ {V' V : Y.AffineZariskiSite} (i : V' ⟶ V), ∃! u : Z V' ⟶ Z V,
      u ≫ h V = h V' ≫ (𝒰Y).trans i ∧ g V' ≫ u = resX f i ≫ g V := fun {V' V} i =>
    Grothendieck.Folder126RadicialEtaleGlobal.existsUnique_lift (g V') (h V' ≫ (𝒰Y).trans i)
      (h V) (resX f i ≫ g V) (by rw [Category.assoc, hgh, resX_snd, ← Category.assoc, hgh])
  let F : Y.AffineZariskiSite ⥤ Scheme.{u} :=
    { obj := Z
      map := fun i => (hu i).exists.choose
      map_id := fun V => ((hu (𝟙 V)).unique (hu (𝟙 V)).exists.choose_spec
        ⟨by rw [Scheme.Cover.trans_id, Category.id_comp, Category.comp_id],
          by rw [resX_id, Category.id_comp, Category.comp_id]⟩)
      map_comp := fun {V'' V' V} i j => by
        refine (hu (i ≫ j)).unique (hu (i ≫ j)).exists.choose_spec ⟨?_, ?_⟩
        · rw [Category.assoc, (hu j).exists.choose_spec.1, ← Category.assoc,
            (hu i).exists.choose_spec.1, Category.assoc, ← Scheme.Cover.trans_comp]
        · rw [← Category.assoc, (hu i).exists.choose_spec.2, Category.assoc,
            (hu j).exists.choose_spec.2, ← Category.assoc, ← resX_comp] }
  have hF : ∀ {V' V : Y.AffineZariskiSite} (i : V' ⟶ V),
      F.map i ≫ h V = h V' ≫ (𝒰Y).trans i ∧ g V' ≫ F.map i = resX f i ≫ g V := fun i =>
    (hu i).exists.choose_spec
  -- The gluing datum: the squares are cartesian.
  let α : F ⟶ (𝒰Y).functorOfLocallyDirected :=
    { app := h
      naturality := fun {V' V} i => (hF i).1 }
  have hα : α.Equifibered := by
    intro V' V i
    have : Etale (h V) := hhe V
    have : UniversalHomeomorphism (g V) := hg V
    have : UniversalHomeomorphism (g V') := hg V'
    have : Etale (h V') := hhe V'
    -- `X_{V'}` is the restriction of `X_V` to `V'`.
    have sqX : IsPullback (resX f i) (pullback.snd f ((𝒰Y).f V')) (pullback.snd f ((𝒰Y).f V))
        ((𝒰Y).trans i) := by
      refine IsPullback.of_right ?_ (resX_snd f i) (IsPullback.of_hasPullback f ((𝒰Y).f V))
      rw [resX_fst, Scheme.Cover.trans_map]
      exact IsPullback.of_hasPullback f ((𝒰Y).f V')
    have hc : (resX f i ≫ g V) ≫ h V = pullback.snd f ((𝒰Y).f V') ≫ (𝒰Y).trans i := by
      rw [Category.assoc, hgh, resX_snd]
    let c : pullback f ((𝒰Y).f V') ⟶ pullback (h V) ((𝒰Y).trans i) := pullback.lift _ _ hc
    have hcf : c ≫ pullback.fst (h V) ((𝒰Y).trans i) = resX f i ≫ g V :=
      pullback.lift_fst _ _ _
    have hcs : c ≫ pullback.snd (h V) ((𝒰Y).trans i) = pullback.snd f ((𝒰Y).f V') :=
      pullback.lift_snd _ _ _
    have sqc : IsPullback c (resX f i) (pullback.fst (h V) ((𝒰Y).trans i)) (g V) := by
      refine IsPullback.of_right ?_ hcf (IsPullback.of_hasPullback (h V) ((𝒰Y).trans i)).flip
      rw [hcs, hgh]
      exact sqX.flip
    have : UniversalHomeomorphism c := MorphismProperty.of_isPullback sqc.flip inferInstance
    obtain ⟨φ, ⟨hφg, hφh⟩, -⟩ :=
      Grothendieck.Folder126RadicialEtaleGlobal.existsUnique_iso_of_factorisations (g V') (h V')
        c (pullback.snd (h V) ((𝒰Y).trans i)) (by rw [hgh, hcs])
    have hmap : φ.hom ≫ pullback.fst (h V) ((𝒰Y).trans i) = F.map i :=
      (hu i).unique ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hφh],
        by rw [← Category.assoc, hφg, hcf]⟩ (hF i)
    exact IsPullback.of_iso_pullback ⟨(hF i).1⟩ φ hmap hφh
  let d : (𝒰Y).RelativeGluingData := ⟨F, α, hα⟩
  have : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  have : ∀ {i j : Y.AffineZariskiSite} (k : i ⟶ j), IsOpenImmersion (d.functor.map k) :=
    fun k => MorphismProperty.of_isPullback (hα k).flip inferInstance
  have : Small.{u} Y.AffineZariskiSite := inferInstance
  have : HasColimit d.functor := inferInstance
  -- The glued scheme and its structure map, finite and étale.
  have hpb : ∀ V, IsPullback (h V) (colimit.ι d.functor V) ((𝒰Y).f V) d.toBase :=
    d.isPullback_natTrans_ι_toBase
  have : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
  have : IsZariskiLocalAtTarget (@IsFinite.{u}) := isZariskiLocalAtTarget_isFinite
  have hEt : Etale d.toBase := by
    refine IsZariskiLocalAtTarget.of_openCover (P := @Etale) (𝒰Y) fun V => ?_
    have : Etale (h V) := hhe V
    change Etale (pullback.snd d.toBase ((𝒰Y).f V))
    rw [← (hpb V).flip.isoPullback_inv_snd]
    infer_instance
  have hFin : IsFinite d.toBase := by
    refine IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (𝒰Y) fun V => ?_
    have : IsFinite (h V) := hh V
    change IsFinite (pullback.snd d.toBase ((𝒰Y).f V))
    rw [← (hpb V).flip.isoPullback_inv_snd]
    infer_instance
  -- The glued map `X ⟶ X^ét`.
  let g₀ : X ⟶ d.glued :=
    Scheme.OpenCover.glueMorphismsOfLocallyDirected ((𝒰Y).pullback₁ f)
      (fun V => g V ≫ colimit.ι d.functor V) fun {V' V} i => by
        change resX f i ≫ g V ≫ colimit.ι d.functor V = g V' ≫ colimit.ι d.functor V'
        rw [← Category.assoc, ← (hF i).2, Category.assoc]
        exact congrArg (g V' ≫ ·) (colimit.w d.functor i)
  have hg₀ : ∀ V, pullback.fst f ((𝒰Y).f V) ≫ g₀ = g V ≫ colimit.ι d.functor V := fun V =>
    Scheme.OpenCover.map_glueMorphismsOfLocallyDirected ((𝒰Y).pullback₁ f) _ _ V
  have key : ∀ V : Y.AffineZariskiSite,
      pullback.fst f ((𝒰Y).f V) ≫ g₀ ≫ d.toBase = pullback.fst f ((𝒰Y).f V) ≫ f := by
    intro V
    rw [← Category.assoc, hg₀, Category.assoc, d.ι_toBase]
    change g V ≫ h V ≫ (𝒰Y).f V = _
    rw [← Category.assoc, hgh]
    exact pullback.condition.symm
  have hgf : g₀ ≫ d.toBase = f :=
    Scheme.Cover.hom_ext ((𝒰Y).pullback₁ f) _ _ fun V => key V
  -- Over `X^ét_V`, `X ⟶ X^ét` is `X_V ⟶ X^ét_V`.
  have hsq : ∀ V, IsPullback (pullback.fst f ((𝒰Y).f V)) (g V) g₀ (colimit.ι d.functor V) :=
    fun V => by
      refine IsPullback.of_bot ?_ (hg₀ V) (hpb V).flip
      rw [hgh, hgf]
      exact IsPullback.of_hasPullback f ((𝒰Y).f V)
  have : IsIntegralHom (g₀ ≫ d.toBase) := by rw [hgf]; infer_instance
  have : IsIntegralHom g₀ := IsIntegralHom.of_comp g₀ d.toBase
  refine ⟨d.glued, g₀, d.toBase,
    universalHomeomorphism_of_hasGeomDegree_one g₀ fun K _ _ p => ?_, hFin, hEt, hgf⟩
  obtain ⟨V, z, hz⟩ : ∃ (V : Y.AffineZariskiSite) (z : Z V),
      colimit.ι d.functor V z = p (IsLocalRing.closedPoint K) :=
    d.cover.exists_eq (p (IsLocalRing.closedPoint K))
  have : IsOpenImmersion (colimit.ι d.functor V) := d.cover.map_prop V
  have hsub : Set.range p.base ⊆ Set.range (colimit.ι d.functor V).base := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
    exact ⟨z, hz⟩
  let p' : Spec (.of K) ⟶ Z V := IsOpenImmersion.lift (colimit.ι d.functor V) p hsub
  have hp' : p' ≫ colimit.ι d.functor V = p := IsOpenImmersion.lift_fac _ _ _
  have : IsFinite (g V) := by
    have : IsFinite (g V ≫ h V) := by rw [hgh]; infer_instance
    have : IsFinite (h V) := hh V
    exact IsFinite.of_comp (g V) (h V)
  have : UniversalHomeomorphism (g V) := hg V
  obtain ⟨e⟩ := hasGeomDegree_one_of_universalHomeomorphism (g V) K p'
  rw [← hp']
  exact ⟨(geomFibreEquivOfIsPullback (hsq V) p').symm.trans e⟩

/-- **Folder 126, pages 17–23, the whole statement.** Let `f : X ⟶ Y` be finite and universally
open with exactly `n` geometric points in every geometric fibre. Then `f` factors as a universal
homeomorphism `X ⟶ X^ét` followed by a finite étale `X^ét ⟶ Y`, and every `Y`-morphism from `X`
to an étale `Y`-scheme factors uniquely through `X ⟶ X^ét`. (The factorisation is unique up to
unique isomorphism, `Grothendieck.Folder126RadicialEtaleGlobal.existsUnique_iso_of_factorisations`.)
-/
@[montpellier "126, 17–23"]
theorem radicial_etale_factorisation (f : X ⟶ Y) [IsFinite f] [UniversallyOpen f] {n : ℕ}
    (hn : HasGeomDegree f n) :
    ∃ (E : Scheme.{u}) (g₀ : X ⟶ E) (h₀ : E ⟶ Y),
      UniversalHomeomorphism g₀ ∧ IsFinite h₀ ∧ Etale h₀ ∧ g₀ ≫ h₀ = f ∧
      ∀ {E' : Scheme.{u}} (e : E' ⟶ Y) [Etale e] (v : X ⟶ E'), v ≫ e = f →
        ∃! u : E ⟶ E', u ≫ e = h₀ ∧ g₀ ≫ u = v := by
  obtain ⟨E, g₀, h₀, hg, hh, he, hgh⟩ := exists_radicial_etale_factorisation_of_hasGeomDegree f hn
  exact ⟨E, g₀, h₀, hg, hh, he, hgh, fun e _ v hv =>
    Grothendieck.Folder126RadicialEtaleGlobal.existsUnique_lift g₀ h₀ e v (hv.trans hgh.symm)⟩

end Grothendieck.Folder126Glue
