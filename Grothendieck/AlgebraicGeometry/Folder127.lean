/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import OpenProblems.Findings.Folder127
public import Grothendieck.RingTheory.Folder127
import Grothendieck.Attr

/-!
# Folder 127, pages 2–3: Lemma 1.3, non-flat descent over an artinian base, affine case

Proof of `OpenProblems.Findings.Folder127.NonFlatDescentArtinian`, the affine case of Lemma 1.3
of folder 127 (finding `127-non-flat-descent-artinian-epimorphism`). Over an artinian base
`Y = Spec A`, the problem of a flat quotient `G` of `F` extending `G_U`, with `G → i_*G_U`
universally injective relative to `Y`, descends along an epimorphism of schemes
`Y' = Spec A' → Y`, flat or not: if the base-changed problem has a solution, so does the
problem over `Y`. The folder states the lemma without proof, and the row asked first whether it
is true. It is, and with fewer hypotheses than the folder takes.

## Main results

* `injective_of_epi_spec`: if `Spec A' → Spec A` is an epimorphism of schemes, then `A → A'` is
  injective.
* `nonFlatDescentArtinian`: the statement `NonFlatDescentArtinian`.
* `nonFlatDescent_of_injective`: the same conclusion with only `A → A'` injective and `N` flat
  over `A`.

## Implementation notes

Write `G = Im(M → N)` and `Q = N/G`. Since `G' = Im(A' ⊗ M → A' ⊗ N)` is the kernel of
`A' ⊗ N → A' ⊗ Q` (right exactness) and its inclusion is universally injective, `A' ⊗ Q` is flat
over `A'` (`flat_of_surjective_of_ker_inf_smul_top_le`; `A' ⊗ N` is flat because `N` is). Flatness
descends along the injection `A → A'` over the artinian ring `A`
(`flat_of_flat_baseChange_of_isArtinianRing`), so `Q` is flat. Then `0 → G → N → Q → 0` with `N`
and `Q` flat gives both conclusions: `G` is flat and `G → N` is universally injective.

**What the proof finds.** The finiteness of `A' → A` and the flatness of `G'` are not used, nor
the hypotheses of `IsAffineSetting` other than the flatness of `N` over `A` (`G_U` flat over `Y`).
An epimorphism is used only through the injectivity of `A → A'`.

## References

* A. Grothendieck, folder 127, pp. 2–3, Lemma 1.3 (finding
  `127-non-flat-descent-artinian-epimorphism`)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct OpenProblems.Findings.Folder127

universe u

namespace Grothendieck.Folder127

/-- An epimorphism of affine schemes `Spec A' → Spec A` comes from an injective ring map: two
elements of `A` with the same image in `A'` give two maps `Spec A → Spec A[X]` that agree on
`Spec A'`. -/
theorem injective_of_epi_spec {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    (h : Epi (Spec.map (CommRingCat.ofHom (algebraMap A A')))) :
    Function.Injective (algebraMap A A') := by
  intro a b hab
  let ev : A → (CommRingCat.of (Polynomial A) ⟶ CommRingCat.of A) := fun c ↦
    CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id A) c)
  have hcomp : ev a ≫ CommRingCat.ofHom (algebraMap A A') =
      ev b ≫ CommRingCat.ofHom (algebraMap A A') := by
    ext1
    apply Polynomial.ringHom_ext
    · intro c; simp [ev]
    · simp [ev, hab]
  have hspec : Spec.map (ev a) = Spec.map (ev b) := by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap A A'))), ← Spec.map_comp,
      ← Spec.map_comp, hcomp]
  simpa [ev] using congrArg (fun φ ↦ φ.hom Polynomial.X) (Spec.map_injective hspec)

/-- **Lemma 1.3 of folder 127, affine case, under the hypotheses the proof uses.** Let `A` be
artinian, `A → A'` injective (flat or not, finite or not), `φ : M → N` a map of `A`-modules with
`N` flat. If the image of `A' ⊗ M` in `A' ⊗ N` has a universally injective inclusion, then the
image `G` of `M` in `N` is flat over `A` and its inclusion into `N` is universally injective. -/
@[montpellier "127, 2–3"]
theorem nonFlatDescent_of_injective {A A' M N : Type u} [CommRing A] [IsArtinianRing A]
    [CommRing A'] [Algebra A A'] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Flat A N] (φ : M →ₗ[A] N) (hinj : Function.Injective (algebraMap A A'))
    (huniv : IsUnivInjectiveRel A' (LinearMap.range (φ.baseChange A')).subtype) :
    IsFlatClosureSolution A φ := by
  set G := LinearMap.range φ
  let p := G.mkQ.baseChange A'
  have hp : Function.Surjective p := LinearMap.lTensor_surjective A' G.mkQ_surjective
  have hφ : G.subtype ∘ₗ φ.rangeRestrict = φ := LinearMap.ext fun _ ↦ rfl
  have hker : LinearMap.ker p = LinearMap.range (φ.baseChange A') := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    change G.mkQ.lTensor A' x = 0 ↔ _
    rw [lTensor_exact A' (LinearMap.exact_subtype_mkQ G) G.mkQ_surjective x]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective A' φ.surjective_rangeRestrict y
      refine ⟨z, ?_⟩
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hφ]
      rfl
    · rintro ⟨z, rfl⟩
      refine ⟨φ.rangeRestrict.lTensor A' z, ?_⟩
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hφ]
      rfl
  have : Module.Flat A' (A' ⊗[A] (N ⧸ G)) :=
    flat_of_surjective_of_ker_inf_smul_top_le p hp fun I ↦ by
      rw [hker]
      exact inf_smul_top_le_of_injective_baseChange _ I (huniv (A' ⧸ I))
  have : Module.Flat A (N ⧸ G) := flat_of_flat_baseChange_of_isArtinianRing hinj
  refine ⟨flat_of_flat_of_flat_cokernel G.injective_subtype (LinearMap.exact_subtype_mkQ G)
    G.mkQ_surjective, fun R'' _ _ ↦ ?_⟩
  exact lTensor_injective_of_flat_cokernel G.injective_subtype (LinearMap.exact_subtype_mkQ G)
    G.mkQ_surjective R''

/-- **`127-non-flat-descent-artinian-epimorphism`** (folder 127, pp. 2–3, Lemma 1.3), in the affine
case: the statement `NonFlatDescentArtinian` holds. The folder states the lemma without proof.
The finiteness of `A → A'` is not used, and the epimorphism only through the injectivity of
`A → A'` (`nonFlatDescent_of_injective`). -/
@[montpellier "127, 2–3"]
theorem nonFlatDescentArtinian : NonFlatDescentArtinian.{u} := by
  intro A B M N _ _ _ _ _ _ _ _ _ _ _ φ g hA hset A' _ _ _ hepi hsol
  have : IsArtinianRing A := hA
  have : Module.Flat A N := hset.2.2.2.2
  exact nonFlatDescent_of_injective (φ.restrictScalars A) (injective_of_epi_spec hepi) hsol.2

end Grothendieck.Folder127
