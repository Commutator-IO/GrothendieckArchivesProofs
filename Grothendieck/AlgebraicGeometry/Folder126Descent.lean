/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Grothendieck.AlgebraicGeometry.Folder126EtaleSplitting
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.UniversalHomeomorphismLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
import Grothendieck.Attr

/-!
# Folder 126, pages 17–22: the factorisation over an étale covering

Finding `126-radicial-etale-factorisation`, existence of `X^ét`, step 3a. Over a quasi-compact
`Y`, the étale-local factorisations of `Grothendieck.Folder126EtaleSplitting` are assembled over a
single étale surjective morphism `w : W ⟶ Y` with `W` affine: finitely many of the neighbourhoods
cover `Y` (it is quasi-compact and étale morphisms are open), `W` is their disjoint union, and the
factorisation over `W` is the disjoint union of the local ones, pullbacks distributing over finite
coproducts of schemes.

This is the covering along which `X^ét` is descended.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Grothendieck.Folder126GeometricPoints Grothendieck.Folder126EtaleSplitting

universe u

namespace Grothendieck.Folder126Descent

variable {X Y : Scheme.{u}}

/-- **The factorisation over one étale covering.** Let `Y` be quasi-compact and `f : X ⟶ Y` finite
and universally open with exactly `n` geometric points in every geometric fibre. There is an étale
surjective `w : W ⟶ Y` with `W` affine such that the base change of `f` along `w` (any pullback
square) factors as a universal homeomorphism followed by a finite étale morphism. -/
@[montpellier "126, 17–22"]
theorem exists_etale_cover_factorisation [CompactSpace Y] (f : X ⟶ Y) [IsFinite f]
    [UniversallyOpen f] {n : ℕ} (hn : HasGeomDegree f n) :
    ∃ (W : Scheme.{u}) (w : W ⟶ Y), Etale w ∧ Surjective w ∧ IsAffine W ∧
      ∃ (T : Scheme.{u}) (a : T ⟶ X) (b : T ⟶ W), IsPullback a b f w ∧
        ∃ (Z : Scheme.{u}) (g : T ⟶ Z) (h : Z ⟶ W),
          UniversalHomeomorphism g ∧ IsFinite h ∧ Etale h ∧ g ≫ h = b := by
  classical
  choose U u hu hUa hy T a b H Z g h hg hh hhe hgh using
    fun y => exists_etale_local_factorisation f hn y
  -- Finitely many neighbourhoods cover `Y`.
  have hopen : ∀ y, IsOpen (Set.range (u y)) := fun y => (u y).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => Set.range (u y)) hopen
    fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  let U' : s → Scheme.{u} := fun i => U i.1
  let T' : s → Scheme.{u} := fun i => T i.1
  let Z' : s → Scheme.{u} := fun i => Z i.1
  let u' : ∀ i, U' i ⟶ Y := fun i => u i.1
  have : ∀ i, Etale (u' i) := fun i => hu i.1
  have : ∀ i, IsAffine (U' i) := fun i => hUa i.1
  let w : (∐ U') ⟶ Y := Sigma.desc u'
  have hw : Etale w := etale_sigmaDesc u' fun i => inferInstance
  have hws : Surjective w := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_iff_forall.2 fun y => ?_)
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hyi⟩
  -- The base change of `f` along `w` is the disjoint union of the local ones.
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct U')
  have H' := hau.isPullback_of_isColimit_left u' w f (fun i : s => a i.1) (fun i : s => b i.1)
    (fun i : s => H i.1) (coproductIsCoproduct T') (by simp [w])
  have : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
  have : IsZariskiLocalAtTarget (@IsFinite.{u}) :=
    isZariskiLocalAtTarget_isFinite
  have : ∀ i : s, UniversalHomeomorphism (g i.1) := fun i => hg i.1
  have : ∀ i : s, IsFinite (h i.1) := fun i => hh i.1
  have : ∀ i : s, Etale (h i.1) := fun i => hhe i.1
  let g' : (∐ T') ⟶ ∐ Z' := Limits.Sigma.map fun i : s => g i.1
  let h' : (∐ Z') ⟶ ∐ U' := Limits.Sigma.map fun i : s => h i.1
  refine ⟨∐ U', w, hw, hws, inferInstance, ∐ T', _, _, H', ∐ Z', g', h',
    IsZariskiLocalAtTarget.sigmaMap _ fun i => inferInstance,
    IsZariskiLocalAtTarget.sigmaMap _ fun i => inferInstance,
    IsZariskiLocalAtTarget.sigmaMap _ fun i => inferInstance, ?_⟩
  refine Sigma.hom_ext _ _ fun i => ?_
  simp only [g', h', Limits.Sigma.map_comp_map, Limits.Sigma.ι_map, Category.assoc] at *
  rw [← Category.assoc, hgh i.1]
  exact (Cofan.IsColimit.fac (coproductIsCoproduct T')
    (fun x : s => b x.1 ≫ (Cofan.mk (∐ U') (Sigma.ι U')).inj x) i).symm

end Grothendieck.Folder126Descent
