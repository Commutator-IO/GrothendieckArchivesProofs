module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
import Grothendieck.Attr

@[expose] public noncomputable section

/-!
# Folder 126, page 17: geometric points of the fibres

Finding `126-radicial-etale-factorisation`, first step towards the existence of `X^ét`. Page 17
states its hypothesis as « the fibres all have the same number `n` of geometric points ». This
file makes that hypothesis a definition for a morphism of schemes and proves what the descent
argument needs from it.

**Definitions.**
* `GeomFibre f p`: the geometric points of `X` over a geometric point `p : Spec K ⟶ Y`, i.e. the
  morphisms `q : Spec K ⟶ X` with `q ≫ f = p`.
* `HasGeomDegree f n`: every geometric fibre of `f`, over an algebraically closed field, is
  finite with exactly `n` points (it is in bijection with `Fin n`, so that an infinite fibre is
  not counted as `0`, as `Nat.card` would).

**Results.**
* `geomFibrePullbackEquiv`, `HasGeomDegree.pullback_snd`: geometric fibres do not change under
  base change, so neither does the degree.
* `universallyInjective_of_forall_subsingleton`: at most one geometric point over every geometric
  point gives universal injectivity (Stacks 01S4, through Mathlib's
  `tfae_universallyInjective`, after passing to an algebraic closure).
* `surjective_of_forall_nonempty`, and conversely `nonempty_geomFibre_of_surjective` for a finite
  surjective morphism (a closed point of the geometric fibre is a rational point, Mathlib's
  `pointOfClosedPoint`).
* `universalHomeomorphism_of_hasGeomDegree_one`: an integral morphism with exactly one geometric
  point over every geometric point is a universal homeomorphism, and
  `hasGeomDegree_one_of_universalHomeomorphism` is the converse for a finite morphism. This is
  the criterion that makes each sheet `W_k → U` of the étale-local splitting a universal
  homeomorphism, once the `n` sheets share the `n` geometric points of every fibre.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Grothendieck.Folder126GeometricPoints

variable {X Y : Scheme.{u}}

/-- The geometric points of `X` over the geometric point `p : Spec K ⟶ Y` of `Y`. -/
@[montpellier "126, 17"]
abbrev GeomFibre (f : X ⟶ Y) {K : Type u} [Field K] (p : Spec (.of K) ⟶ Y) : Type u :=
  {q : Spec (.of K) ⟶ X // q ≫ f = p}

/-- **The hypothesis of page 17.** Every geometric fibre of `f` has exactly `n` points. -/
@[montpellier "126, 17"]
def HasGeomDegree (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
    Nonempty (GeomFibre f p ≃ Fin n)

/-- The geometric fibre of a base change `X ×_Y U ⟶ U` over `p` is the geometric fibre of
`X ⟶ Y` over the image of `p`. -/
@[montpellier "126, 17"]
def geomFibrePullbackEquiv (f : X ⟶ Y) {U : Scheme.{u}} (u : U ⟶ Y) {K : Type u} [Field K]
    (p : Spec (.of K) ⟶ U) : GeomFibre (pullback.snd f u) p ≃ GeomFibre f (p ≫ u) where
  toFun q := ⟨q.1 ≫ pullback.fst f u, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, q.2]⟩
  invFun q := ⟨pullback.lift q.1 p q.2, pullback.lift_snd _ _ _⟩
  left_inv q := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans q.2.symm))
  right_inv q := Subtype.ext (pullback.lift_fst _ _ _)

/-- The degree of the geometric fibres is stable under base change. -/
@[montpellier "126, 17"]
theorem HasGeomDegree.pullback_snd {f : X ⟶ Y} {n : ℕ} (hf : HasGeomDegree f n)
    {U : Scheme.{u}} (u : U ⟶ Y) : HasGeomDegree (pullback.snd f u) n := fun K _ _ p =>
  (hf K _).map fun e => (geomFibrePullbackEquiv f u p).trans e

/-- At most one geometric point over every geometric point: `f` is universally injective. -/
@[montpellier "126, 17"]
theorem universallyInjective_of_forall_subsingleton (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
      Subsingleton (GeomFibre f p)) :
    UniversallyInjective f := by
  refine ((tfae_universallyInjective f).out 1 2).2 ?_
  intro K _ g₁ g₂ hg
  have hg : g₁ ≫ f = g₂ ≫ f := hg
  let L := AlgebraicClosure K
  let ι : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : Epi ι := Flat.epi_of_flat_of_surjective _
  have := h L (ι ≫ g₁ ≫ f)
  have heq : (⟨ι ≫ g₁, Category.assoc _ _ _⟩ : GeomFibre f (ι ≫ g₁ ≫ f)) =
      ⟨ι ≫ g₂, by rw [Category.assoc, hg]⟩ := Subsingleton.elim _ _
  exact (cancel_epi ι).1 (congrArg Subtype.val heq)

/-- At least one geometric point over every geometric point: `f` is surjective. -/
@[montpellier "126, 17"]
theorem surjective_of_forall_nonempty (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
      Nonempty (GeomFibre f p)) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  let L := AlgebraicClosure (Y.residueField y)
  let φ : Y.residueField y ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap (Y.residueField y) L)
  obtain ⟨q, hq⟩ := h L (Spec.map φ ≫ Y.fromSpecResidueField y)
  let pt : Spec (.of L) := IsLocalRing.closedPoint L
  refine ⟨q pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- A finite surjective morphism has a geometric point over every geometric point: a closed point
of the geometric fibre, which is finite over an algebraically closed field, is rational. -/
@[montpellier "126, 17"]
theorem nonempty_geomFibre_of_surjective (f : X ⟶ Y) [IsFinite f] [Surjective f]
    {K : Type u} [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y) :
    Nonempty (GeomFibre f p) := by
  have : Surjective (pullback.snd f p) := inferInstance
  have : IsFinite (pullback.snd f p) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd f p).surjective (IsLocalRing.closedPoint K)
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton isClosed_univ ⟨z, Set.mem_univ _⟩
  refine ⟨⟨pointOfClosedPoint (pullback.snd f p) x hx ≫ pullback.fst f p, ?_⟩⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

/-- **The criterion.** An integral morphism with exactly one geometric point over every
geometric point is a universal homeomorphism. -/
@[montpellier "126, 17"]
theorem universalHomeomorphism_of_hasGeomDegree_one (f : X ⟶ Y) [IsIntegralHom f]
    (h : HasGeomDegree f 1) : UniversalHomeomorphism f :=
  (universalHomeomorphism_iff_integral_universallyInjective_surjective f).2
    ⟨inferInstance,
      universallyInjective_of_forall_subsingleton f fun K _ _ p =>
        (h K p).elim fun e => e.subsingleton,
      surjective_of_forall_nonempty f fun K _ _ p => (h K p).elim fun e => ⟨e.symm 0⟩⟩

/-- Conversely, a finite universal homeomorphism has exactly one geometric point over every
geometric point. -/
@[montpellier "126, 17"]
theorem hasGeomDegree_one_of_universalHomeomorphism (f : X ⟶ Y) [IsFinite f]
    [UniversalHomeomorphism f] : HasGeomDegree f 1 := by
  obtain ⟨-, hinj, hsurj⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).1 inferInstance
  intro K _ _ p
  obtain ⟨q₀⟩ := nonempty_geomFibre_of_surjective f p
  have hsub : Subsingleton (GeomFibre f p) := ⟨fun q₁ q₂ => Subtype.ext ?_⟩
  · exact ⟨Equiv.ofBijective (fun _ : GeomFibre f p => (0 : Fin 1))
      ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨q₀, Subsingleton.elim _ _⟩⟩⟩
  have key : ∀ (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f) :=
    ((tfae_universallyInjective f).out 1 2).1 hinj
  exact key K (q₁.2.trans q₂.2.symm)

end Grothendieck.Folder126GeometricPoints
