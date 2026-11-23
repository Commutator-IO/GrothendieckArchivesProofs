/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import StacksCore.RingTheory.Nakayama
import Grothendieck.Attr

/-!
# Folder 127, pages 2–3: flatness descends along injective maps over an artinian ring

Lemma 1.3 of folder 127 (finding `127-non-flat-descent-artinian-epimorphism` of
`src/content/findings.ts`) says that, over an artinian base `Y`, the problem of a flat quotient
`G` of `F` extending `G_U`, with `G → i_*G_U` universally injective relative to `Y`, descends along
an epimorphism `Y' → Y` that need not be flat. The commutative algebra the lemma turns on is the
descent of flatness itself, which is proved here: over an artinian ring `A`, a module `Q` is flat
as soon as `A' ⊗_A Q` is flat over `A'` for one ring map `A → A'` that is injective. No flatness
and no finiteness of `A'` is needed, and `Q` is arbitrary.

## Main results

* `flat_of_flat_baseChange_of_isNilpotent`: `A` local with nilpotent maximal ideal `𝔪`,
  `A → A'` injective, `A' ⊗_A Q` flat over `A'`. Then `Q` is flat (it is even free).
* `flat_of_flat_baseChange_of_isArtinianRing`: the same over any artinian ring, by localisation
  at the maximal ideals.
* `flat_of_surjective_of_ker_inf_smul_top_le`: a quotient of a flat module by a submodule `K`
  with `K ∩ I N ⊆ I K` for every ideal `I` is flat; `inf_smul_top_le_of_injective_baseChange`
  gives that condition from the injectivity of `K ⊗ R/I → N ⊗ R/I`, through
  `one_tmul_eq_zero_iff` (`1 ⊗ x = 0` in `R/I ⊗ N` iff `x ∈ I N`).

These are used in `Grothendieck/AlgebraicGeometry/Folder127.lean` to prove the affine statement
`OpenProblems.Findings.Folder127.NonFlatDescentArtinian`.

## Implementation notes

The proof of the local case: lift a basis of `Q/𝔪Q` over `A/𝔪` to a family `x` of `Q`, and let
`π : A^(ι) → Q` be its linear combination. Nakayama's lemma for the nilpotent ideal `𝔪` (Stacks
00DV (9) and (10), `StacksCore.RingTheory.Nakayama`) makes `π` surjective, and the linear
independence of the reductions gives `ker π ⊆ 𝔪 A^(ι)`. After base change,
`π' : A'^(ι) → A' ⊗ Q` is surjective onto a flat module, so `ker π' ∩ J A'^(ι) = J ker π'` for
`J = 𝔪A'` (`LinearMap.ker_inf_smul_top_eq_smul_of_flat`), and `ker π' ⊆ J A'^(ι)` by right
exactness. Hence `ker π' ⊆ J ker π'`, so `ker π' = 0` because `J` is nilpotent. Finally
`A^(ι) → A'^(ι)` is injective because `A → A'` is (`Module.Flat.tensorProduct_mk_injective`), so
`ker π = 0` and `Q ≅ A^(ι)`.

## References

* A. Grothendieck, folder 127, pp. 2–3, Lemma 1.3 (finding
  `127-non-flat-descent-artinian-epimorphism`)
-/

@[expose] public section

open TensorProduct

namespace Grothendieck.Folder127

/-- Right exactness of base change: if `ker π ⊆ I • ⊤` and `π` is surjective, then the kernel of
`π ⊗ R'` lies in `(I R') • ⊤`. -/
theorem ker_baseChange_le_smul_top {R R' F Q : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    [AddCommGroup F] [Module R F] [AddCommGroup Q] [Module R Q] {I : Ideal R} (π : F →ₗ[R] Q)
    (hsurj : Function.Surjective π) (hker : LinearMap.ker π ≤ I • ⊤) :
    LinearMap.ker (π.baseChange R') ≤ I.map (algebraMap R R') • ⊤ := by
  have htmul : ∀ (r' : R'), ∀ f ∈ I • (⊤ : Submodule R F),
      r' ⊗ₜ[R] f ∈ I.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] F)) := by
    intro r' f hf
    refine Submodule.smul_induction_on hf (fun a ha f _ ↦ ?_) (fun f g hf hg ↦ ?_)
    · rw [TensorProduct.tmul_smul, ← algebraMap_smul R' a]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
    · rw [TensorProduct.tmul_add]; exact add_mem hf hg
  intro y hy
  obtain ⟨z, rfl⟩ := (lTensor_exact R' (LinearMap.exact_subtype_ker_map π) hsurj y).1
    (LinearMap.mem_ker.1 hy)
  clear hy
  induction z using TensorProduct.inductionOn with
  | tmul r' k => exact htmul r' k (hker k.2)
  | add z w hz hw => rw [map_add]; exact add_mem hz hw

/-- **Flatness descends along an injective map over a local ring with nilpotent maximal ideal**
(folder 127, Lemma 1.3, its flatness part). Let `R` be a local ring whose maximal ideal is
nilpotent (an artinian local ring, for instance), `R → R'` an injective ring map, flat or not,
and `Q` an `R`-module. If `R' ⊗_R Q` is flat over `R'`, then `Q` is flat over `R`. -/
@[montpellier "127, 2–3"]
theorem flat_of_flat_baseChange_of_isNilpotent {R R' Q : Type*} [CommRing R] [IsLocalRing R]
    [CommRing R'] [Algebra R R'] [AddCommGroup Q] [Module R Q]
    (hR : IsNilpotent (IsLocalRing.maximalIdeal R))
    (hinj : Function.Injective (algebraMap R R')) [Module.Flat R' (R' ⊗[R] Q)] :
    Module.Flat R Q := by
  set m := IsLocalRing.maximalIdeal R
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let b := Module.Basis.ofVectorSpace (R ⧸ m) (Q ⧸ m • (⊤ : Submodule R Q))
  choose x hx using fun i ↦ Submodule.mkQ_surjective (m • (⊤ : Submodule R Q)) (b i)
  let π : (_ →₀ R) →ₗ[R] Q := Finsupp.linearCombination R x
  have hπ : ∀ i r, (m • (⊤ : Submodule R Q)).mkQ (π (Finsupp.single i r)) =
      Ideal.Quotient.mk m r • b i := by
    intro i r
    simp only [π, Finsupp.linearCombination_single, map_smul, hx, Module.IsTorsionBySet.mk_smul]
  -- `π` is surjective, by Nakayama's lemma for the nilpotent ideal `m`.
  have hmap : Submodule.map (m • (⊤ : Submodule R Q)).mkQ (LinearMap.range π) = ⊤ := by
    refine eq_top_iff.2 fun v _ ↦ ?_
    rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (b.repr v i)
    simpa only [← hr, ← hπ] using Submodule.mem_map_of_mem (LinearMap.mem_range_self π _)
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top]
    refine eq_top_iff.2 (Submodule.le_of_le_smul_of_isNilpotent hR (le_of_eq ?_))
    rw [sup_comm, ← Submodule.comap_map_mkQ, hmap, Submodule.comap_top]
  -- `ker π ⊆ m R^(ι)`, by linear independence of the reductions.
  have hred : ∀ c, (m • (⊤ : Submodule R Q)).mkQ (π c) =
      Finsupp.linearCombination (R ⧸ m) b (c.mapRange (Ideal.Quotient.mk m) (map_zero _)) := by
    intro c
    induction c using Finsupp.induction_linear <;> simp_all [Finsupp.mapRange_add]
  have hker : LinearMap.ker π ≤ m • ⊤ := fun c hc ↦ by
    have h0 : c.mapRange (Ideal.Quotient.mk m) (map_zero _) = 0 :=
      b.linearIndependent (by rw [← hred, LinearMap.mem_ker.1 hc, map_zero, map_zero])
    rw [← c.sum_single]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [← Finsupp.smul_single_one]
    exact Submodule.smul_mem_smul
      (Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using DFunLike.congr_fun h0 i)) trivial
  -- After base change, `π'` is injective.
  let π' := π.baseChange R'
  have hsurj' : Function.Surjective π' := LinearMap.lTensor_surjective R' hsurj
  set J := m.map (algebraMap R R')
  have hbot' : LinearMap.ker π' = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_isNilpotent J _ (hR.map (Ideal.mapHom _)) <| by
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat J π' hsurj']
    exact le_inf le_rfl (ker_baseChange_le_smul_top π hsurj hker)
  -- Hence `π` is injective, since `R^(ι) → R'^(ι)` is.
  have := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
  have hinjπ : Function.Injective π := fun c d h ↦ Module.Flat.tensorProduct_mk_injective R _ R'
    (LinearMap.ker_eq_bot.1 hbot' (by simp [π', h]))
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective π ⟨hinjπ, hsurj⟩).symm

/-- **Flatness descends along an injective map over an artinian ring** (folder 127, Lemma 1.3, its
flatness part). Let `A` be an artinian ring, `A → A'` an injective ring map, flat or not, and `Q`
an `A`-module. If `A' ⊗_A Q` is flat over `A'`, then `Q` is flat over `A`. -/
@[montpellier "127, 2–3"]
theorem flat_of_flat_baseChange_of_isArtinianRing {A A' Q : Type*} [CommRing A] [IsArtinianRing A]
    [CommRing A'] [Algebra A A'] [AddCommGroup Q] [Module A Q]
    (hinj : Function.Injective (algebraMap A A')) [Module.Flat A' (A' ⊗[A] Q)] :
    Module.Flat A Q := by
  refine Module.flat_of_isLocalized_maximal A Q (fun P _ ↦ Localization.AtPrime P ⊗[A] Q)
    (fun P _ ↦ TensorProduct.mk A (Localization.AtPrime P) Q 1) fun P _ ↦ ?_
  let A'ₚ := Localization (Algebra.algebraMapSubmonoid A' P.primeCompl)
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (Localization.AtPrime P)) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hinjₚ : Function.Injective (algebraMap (Localization.AtPrime P) A'ₚ) :=
    localizationAlgebra_injective _ _ hinj
  have : Module.Flat A'ₚ (A'ₚ ⊗[Localization.AtPrime P] (Localization.AtPrime P ⊗[A] Q)) :=
    Module.Flat.of_linearEquiv
      ((AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime P) A'ₚ A'ₚ Q).trans
        (AlgebraTensorModule.cancelBaseChange A A' A'ₚ A'ₚ Q).symm)
  have : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[A] Q) :=
    flat_of_flat_baseChange_of_isNilpotent hnil hinjₚ
  exact Module.Flat.trans A (Localization.AtPrime P) _

/-! ### Flat quotients and universal injectivity -/

section Purity

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

/-- `1 ⊗ x` vanishes in `R ⧸ I ⊗ N` exactly when `x ∈ I N`. -/
theorem one_tmul_eq_zero_iff (I : Ideal R) (x : N) :
    (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R N) := by
  rw [← (quotTensorEquivQuotSMul N I).injective.eq_iff, map_zero,
    ← map_one (Ideal.Quotient.mk I),
    quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]

/-- If the inclusion of `K` into `N` stays injective after base change to `R ⧸ I`, then
`K ∩ I N = I K`. -/
theorem inf_smul_top_le_of_injective_baseChange (K : Submodule R N) (I : Ideal R)
    (hK : Function.Injective (K.subtype.baseChange (R ⧸ I))) :
    K ⊓ I • ⊤ ≤ I • K := by
  rintro x ⟨hxK, hxI⟩
  rw [← Submodule.mem_smul_top_iff I K ⟨x, hxK⟩, ← one_tmul_eq_zero_iff]
  exact hK (by rwa [LinearMap.baseChange_tmul, map_zero, Submodule.subtype_apply,
    one_tmul_eq_zero_iff])

/-- A surjection `p : N → Q` from a flat module whose kernel `K` satisfies `K ∩ I N ⊆ I K` for
every ideal `I` (a pure submodule) has a flat target. -/
theorem flat_of_surjective_of_ker_inf_smul_top_le {Q : Type*} [AddCommGroup Q] [Module R Q]
    [Module.Flat R N] (p : N →ₗ[R] Q) (hp : Function.Surjective p)
    (h : ∀ I : Ideal R, LinearMap.ker p ⊓ I • ⊤ ≤ I • LinearMap.ker p) : Module.Flat R Q := by
  refine Module.Flat.iff_rTensor_injective'.2 fun I ↦ (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective I hp x
  let μN := (TensorProduct.lid R N).toLinearMap ∘ₗ I.subtype.rTensor N
  let K := LinearMap.ker p
  let μK := (TensorProduct.lid R K).toLinearMap ∘ₗ I.subtype.rTensor K
  have comm : p ∘ₗ μN =
      (TensorProduct.lid R Q).toLinearMap ∘ₗ I.subtype.rTensor Q ∘ₗ p.lTensor I := by
    ext; simp [μN]
  have hμ : μN y ∈ K := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, comm, LinearMap.comp_apply, LinearMap.comp_apply,
      hx, map_zero]
  have hmem : (⟨μN y, hμ⟩ : K) ∈ I • (⊤ : Submodule R K) := by
    rw [Submodule.mem_smul_top_iff]
    refine h I ⟨hμ, ?_⟩
    rw [← Ideal.subtype_rTensor_range]
    exact ⟨y, rfl⟩
  rw [← Ideal.subtype_rTensor_range] at hmem
  obtain ⟨z, hz⟩ := hmem
  have comm2 : μN ∘ₗ K.subtype.lTensor I = K.subtype ∘ₗ μK := by ext; simp [μN, μK]
  have hinjN : Function.Injective μN :=
    (TensorProduct.lid R N).injective.comp (Module.Flat.iff_rTensor_injective'.1 ‹_› I)
  have hy : K.subtype.lTensor I z = y := hinjN <| by
    rw [← LinearMap.comp_apply, comm2, LinearMap.comp_apply]; exact congrArg Subtype.val hz
  rw [← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    LinearMap.comp_ker_subtype, LinearMap.lTensor_zero, LinearMap.zero_apply]

end Purity

end Grothendieck.Folder127
