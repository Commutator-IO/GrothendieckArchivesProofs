/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcEffectivity
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.CanonicalInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.OpenSubDatum
import Grothendieck.Attr

/-!
# Buffalo, algebraic geometry, part 09: effective descent of schemes along fpqc morphisms

`Part09a.lean` left three entries of `vuys5SNs2eQ` (10 July 1973) unformalised, Mathlib having no
category of descent data of schemes relative to `g : S' ⟶ S`. They are treated here from
AxiomMath/Stacks (Apache-2.0), where a descent datum relative to `g` is
`AlgebraicGeometry.DescentDatum g`: a scheme `X'` over `S'` with an isomorphism
`X' ×_S S' ≅ S' ×_S X'` over `S' ×_S S'` satisfying the cocycle condition (Stacks 023V); it is
effective when it is isomorphic to the canonical datum of a scheme over `S`.

## Main results

Throughout `g : S' ⟶ S` is surjective, flat and quasi-compact (faithfully flat quasi-compact, as
in the lecture).

* `prop_16640` (16640, 4:37:20): if `X'` is covered by stable opens `X'_i`, the datum on `X'` is
  effective if and only if the induced data on the `X'_i` are. « If » is Stacks 0AP4
  (`isEffective_of_forall_exists_restrictOpen`); « only if » transports a stable open along an
  isomorphism with a canonical datum, whose stable opens are the inverse images of opens of the
  descended scheme (`isEffective_restrictOpen_canonical`).
* `prop_17552` (17552, 4:52:32): if `X'` is covered by stable opens affine over `S'`, the datum is
  effective. Each restricted datum is effective by the one-member case of Stacks 0245
  (`isEffective_of_isAffineHom`), and one concludes by `prop_16640`. The case of `X'` itself
  affine over `S'` (descent of quasi-coherent algebras) is `prop_17552_affine`.

## Implementation notes

The lecture's statements are local on stable opens covering `X'`; the indexed family `X'_i` is
rendered as « every point has a stable open neighbourhood with the property », which is
equivalent.

## Not formalised

18219 (5:03:39): for a separable quadratic extension `k'/k`, a proper smooth non-projective
threefold over `k'` (Hironaka's example) with a non-effective descent datum. The statement is
correct (SGA 1 VIII 7.7), but neither Mathlib nor Stacks has Hironaka's construction; it shows
that the affineness hypothesis of `prop_17552` cannot be dropped, so effective descent of
arbitrary schemes along fpqc morphisms fails.

## References

* the Buffalo lectures on algebraic geometry (1973), 10 July 1973, video `vuys5SNs2eQ`, entries
  16640 (4:37:20), 17552 (4:52:32), 18219 (5:03:39)
* [SGA 1] exposé VIII, 7.7
* Stacks Project, tags 023V, 0AP4, 0245
-/

@[expose] public section


open CategoryTheory

universe u

namespace Buffalo.AG.Part09

open AlgebraicGeometry

/-- vuys5SNs2eQ-16640 (4:37:20) [prop] Let `g : S' ⟶ S` be faithfully flat and quasi-compact and
`D` a descent datum on `X'` relative to `g`. If `X'` is covered by stable opens, `D` is effective
if and only if the induced data on these opens are. The second item: the restriction of an
effective datum to any stable open is effective. Stacks 0AP4. -/
@[buffalo "vuys5SNs2eQ-16640"]
theorem prop_16640 {S S' : Scheme.{u}} {g : S' ⟶ S} [Surjective g] [Flat g] [QuasiCompact g]
    (D : DescentDatum g) :
    ((∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) ↔
      DescentData.IsEffective D) ∧
    (DescentData.IsEffective D → ∀ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
      DescentData.IsEffective (D.restrictOpen W hW)) := by
  have hres : DescentData.IsEffective D → ∀ (W : D.over.left.Opens)
      (hW : D.IsTransitionInvariant W), DescentData.IsEffective (D.restrictOpen W hW) := by
    rintro ⟨U, ⟨e⟩⟩ W hW
    let i : D.restrictOpen W hW ⟶ (DescentData.canonicalFunctor g).obj U :=
      D.restrictOpenHom W hW ≫ e.inv
    have : IsOpenImmersion (i.hom ()).left := by
      change IsOpenImmersion ((D.restrictOpenHom W hW).hom () ≫ e.inv.hom ()).left
      rw [Over.comp_left]
      have hleft : IsOpenImmersion ((D.restrictOpenHom W hW).hom ()).left := by
        infer_instance
      have hiso : IsIso (e.inv.hom ()).left :=
        ⟨⟨(e.hom.hom ()).left, congrArg (fun φ ↦ (φ.hom ()).left) e.inv_hom_id,
          congrArg (fun φ ↦ (φ.hom ()).left) e.hom_inv_id⟩⟩
      have hright : IsOpenImmersion (e.inv.hom ()).left :=
        IsOpenImmersion.of_isIso (e.inv.hom ()).left
      exact @IsOpenImmersion.comp _ _ _ _ _ hleft hright
    exact (DescentData.isEffective_restrictOpen_canonical g U _
      (DescentDatum.isTransitionInvariant_opensRange i)).ofIso
      (DescentDatum.restrictOpenIsoOpensRange i).symm
  refine ⟨⟨DescentDatum.isEffective_of_forall_exists_restrictOpen D, fun hD v ↦ ?_⟩, hres⟩
  exact ⟨⊤, DescentDatum.isTransitionInvariant_top D, trivial, hres hD ⊤ _⟩

/-- vuys5SNs2eQ-17552 (4:52:32) [prop], the case `X'` affine over `S'`: along a faithfully flat
quasi-compact `g : S' ⟶ S`, a descent datum on a scheme affine over `S'` (a quasi-coherent
`𝒪_{S'}`-algebra with descent datum) is effective. Stacks 0245, one-member covering. -/
@[buffalo "vuys5SNs2eQ-17552"]
theorem prop_17552_affine {S S' : Scheme.{u}} {g : S' ⟶ S} [Surjective g] [Flat g]
    [QuasiCompact g] (D : DescentDatum g) (haff : IsAffineHom D.over.hom) :
    DescentData.IsEffective D :=
  DescentDatum.isEffective_of_isAffineHom D haff

/-- vuys5SNs2eQ-17552 (4:52:32) [prop] If `g : S' ⟶ S` is faithfully flat and quasi-compact and
`X'` is covered by opens `X'_i` stable under the descent datum and affine over `S'`, the descent
datum on `X'` is effective. Stacks 0245 and 0AP4. -/
@[buffalo "vuys5SNs2eQ-17552"]
theorem prop_17552 {S S' : Scheme.{u}} {g : S' ⟶ S} [Surjective g] [Flat g] [QuasiCompact g]
    (D : DescentDatum g)
    (h : ∀ v : D.over.left, ∃ (W : D.over.left.Opens) (_ : D.IsTransitionInvariant W),
      v ∈ W ∧ IsAffineHom (W.ι ≫ D.over.hom)) :
    DescentData.IsEffective D := by
  refine (prop_16640 D).1.1 fun v ↦ ?_
  obtain ⟨W, hW, hv, haff⟩ := h v
  exact ⟨W, hW, hv, prop_17552_affine (D.restrictOpen W hW) haff⟩

end Buffalo.AG.Part09
