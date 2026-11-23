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
  gives that condition from the injectivity of `K ⊗ R/I → N ⊗ R/I`.
* `lTensor_injective_of_flat_cokernel`, `flat_of_flat_of_flat_cokernel`: for
  `0 → G → N → Q → 0` exact with `Q` flat, `L ⊗ G → L ⊗ N` is injective for every `L`, and `G` is
  flat if `N` is.

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
`A^(ι) → A'^(ι)` is injective because `A → A'` is, so `ker π = 0` and `Q ≅ A^(ι)`.

## References

* A. Grothendieck, folder 127, pp. 2–3, Lemma 1.3 (finding
  `127-non-flat-descent-artinian-epimorphism`)
-/

@[expose] public section

open TensorProduct

namespace Grothendieck.Folder127

/-- A finitely supported family all of whose coefficients lie in `I` lies in `I • ⊤`. -/
theorem mem_smul_top_of_forall_mem {R ι : Type*} [CommRing R] {I : Ideal R} (c : ι →₀ R)
    (hc : ∀ i, c i ∈ I) : c ∈ I • (⊤ : Submodule R (ι →₀ R)) := by
  rw [← c.sum_single]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [← Finsupp.smul_single_one]
  exact Submodule.smul_mem_smul (hc i) Submodule.mem_top

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
    · rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hf hg
  intro y hy
  obtain ⟨z, rfl⟩ := (lTensor_exact R' (LinearMap.exact_subtype_ker_map π) hsurj y).1
    (LinearMap.mem_ker.1 hy)
  clear hy
  induction z using TensorProduct.inductionOn with
  | tmul r' k => exact htmul r' k (hker k.2)
  | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw

/-- For `F` flat (free, for instance) and `R → R'` injective, `F → R' ⊗_R F` is injective. -/
theorem injective_one_tmul {R R' F : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    [AddCommGroup F] [Module R F] [Module.Flat R F] (hinj : Function.Injective (algebraMap R R')) :
    Function.Injective fun c : F ↦ (1 : R') ⊗ₜ[R] c := by
  have := Module.Flat.rTensor_preserves_injective_linearMap (M := F) (Algebra.linearMap R R') hinj
  intro c d hcd
  apply (TensorProduct.lid R F).symm.injective
  apply this
  simpa using hcd

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
    simp only [π, Finsupp.linearCombination_single, map_smul, hx]
    exact (algebraMap_smul (R ⧸ m) r (b i)).symm
  -- `π` is surjective, by Nakayama's lemma for the nilpotent ideal `m`.
  have hmap : Submodule.map (m • (⊤ : Submodule R Q)).mkQ (LinearMap.range π) = ⊤ := by
    refine eq_top_iff.2 fun v _ ↦ ?_
    rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (b.repr v i)
    rw [← hr]
    simp only
    rw [← hπ]
    exact Submodule.mem_map_of_mem (LinearMap.mem_range_self π _)
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top]
    refine eq_top_iff.2 (Submodule.le_of_le_smul_of_isNilpotent hR (le_of_eq ?_))
    rw [sup_comm, ← Submodule.comap_map_mkQ, hmap, Submodule.comap_top]
  -- `ker π ⊆ m R^(ι)`, by linear independence of the reductions.
  have hred : ∀ c, (m • (⊤ : Submodule R Q)).mkQ (π c) =
      Finsupp.linearCombination (R ⧸ m) b (c.mapRange (Ideal.Quotient.mk m) (map_zero _)) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [map_add, map_add, hf, hg, Finsupp.mapRange_add (map_add _), map_add]
    | single i r => rw [hπ, Finsupp.mapRange_single, Finsupp.linearCombination_single]
  have hker : LinearMap.ker π ≤ m • ⊤ := by
    intro c hc
    have h0 : c.mapRange (Ideal.Quotient.mk m) (map_zero _) = 0 :=
      b.linearIndependent (by rw [← hred, LinearMap.mem_ker.1 hc, map_zero, map_zero])
    exact mem_smul_top_of_forall_mem c fun i ↦
      Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using DFunLike.congr_fun h0 i)
  -- After base change, `π'` is injective.
  let π' := π.baseChange R'
  have hsurj' : Function.Surjective π' := LinearMap.lTensor_surjective R' hsurj
  set J := m.map (algebraMap R R')
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hR
    exact ⟨n, by rw [← Ideal.map_pow, hn]; simp⟩
  have hker' : LinearMap.ker π' ≤ J • ⊤ := ker_baseChange_le_smul_top π hsurj hker
  have hbot' : LinearMap.ker π' = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_isNilpotent J _ hJ ?_
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat J π' hsurj']
    exact le_inf le_rfl hker'
  -- Hence `π` is injective, since `R^(ι) → R'^(ι)` is.
  have hinjπ : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    have : (1 : R') ⊗ₜ[R] c ∈ LinearMap.ker π' := by
      rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.1 hc, tmul_zero]
    rw [hbot', Submodule.mem_bot, ← tmul_zero (M := R') (_ →₀ R) (1 : R')] at this
    exact injective_one_tmul hinj this
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

/-- If the inclusion of `K` into `N` stays injective after base change to `R ⧸ I`, then
`K ∩ I N = I K`. -/
theorem inf_smul_top_le_of_injective_baseChange (K : Submodule R N) (I : Ideal R)
    (hK : Function.Injective (K.subtype.baseChange (R ⧸ I))) :
    K ⊓ I • ⊤ ≤ I • K := by
  rintro x ⟨hxK, hxI⟩
  have h0 : (1 : R ⧸ I) ⊗ₜ[R] x = 0 := by
    apply (quotTensorEquivQuotSMul N I).injective
    rw [map_zero, show (1 : R ⧸ I) = Ideal.Quotient.mk I 1 from (map_one _).symm,
      quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]
    exact hxI
  have h1 : (1 : R ⧸ I) ⊗ₜ[R] (⟨x, hxK⟩ : K) = 0 :=
    hK (by rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, map_zero, h0])
  have h2 := congrArg (quotTensorEquivQuotSMul K I) h1
  rw [map_zero, show (1 : R ⧸ I) = Ideal.Quotient.mk I 1 from (map_one _).symm,
    quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero] at h2
  exact (Submodule.mem_smul_top_iff I K ⟨x, hxK⟩).1 h2

/-- A surjection `p : N → Q` from a flat module whose kernel `K` satisfies `K ∩ I N ⊆ I K` for
every ideal `I` (a pure submodule) has a flat target. -/
theorem flat_of_surjective_of_ker_inf_smul_top_le {Q : Type*} [AddCommGroup Q] [Module R Q]
    [Module.Flat R N] (p : N →ₗ[R] Q) (hp : Function.Surjective p)
    (h : ∀ I : Ideal R, LinearMap.ker p ⊓ I • ⊤ ≤ I • LinearMap.ker p) : Module.Flat R Q := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective I hp x
  let μN := (TensorProduct.lid R N).toLinearMap ∘ₗ I.subtype.rTensor N
  let K := LinearMap.ker p
  let μK := (TensorProduct.lid R K).toLinearMap ∘ₗ I.subtype.rTensor K
  have comm : p ∘ₗ μN =
      (TensorProduct.lid R Q).toLinearMap ∘ₗ I.subtype.rTensor Q ∘ₗ p.lTensor I := by
    ext; simp [μN]
  have hμ : μN y ∈ K := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, comm]
    simp only [LinearMap.comp_apply, LinearMap.mem_ker.1 hx, map_zero]
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
  have hy : K.subtype.lTensor I z = y := by
    apply hinjN
    rw [← LinearMap.comp_apply, comm2, LinearMap.comp_apply]
    exact congrArg Subtype.val hz
  rw [Submodule.mem_bot, ← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    show p ∘ₗ K.subtype = 0 from LinearMap.ext fun k ↦ k.2, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

/-- `lTensor` and `rTensor` commute: both composites are `TensorProduct.map u v`. -/
theorem lTensor_rTensor_comm {X Y P P' : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P'] (u : X →ₗ[R] Y)
    (v : P →ₗ[R] P') (t : X ⊗[R] P) :
    v.lTensor Y (u.rTensor P t) = u.rTensor P' (v.lTensor X t) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/-- The diagram chase behind `lTensor_injective_of_flat_cokernel`, for a surjection `ε : F → L`
from a flat module. -/
theorem lTensor_injective_of_flat_cokernel_aux {G Q F L : Type*} [AddCommGroup G] [Module R G]
    [AddCommGroup Q] [Module R Q] [Module.Flat R Q] [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup L] [Module R L] {f : G →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (ε : F →ₗ[R] L) (hε : Function.Surjective ε) : Function.Injective (f.lTensor L) := by
  let K := LinearMap.ker ε
  have hFinj : Function.Injective (f.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hQinj : Function.Injective (K.subtype.rTensor Q) :=
    Module.Flat.rTensor_preserves_injective_linearMap K.subtype K.injective_subtype
  intro x₁ x₂ hx
  rw [← sub_eq_zero] at hx ⊢
  rw [← map_sub] at hx
  generalize x₁ - x₂ = x at hx ⊢
  obtain ⟨x', rfl⟩ := LinearMap.rTensor_surjective G hε x
  obtain ⟨z, hz⟩ := ((rTensor_exact N (LinearMap.exact_subtype_ker_map ε) hε) (f.lTensor F x')).1
    (by rw [← lTensor_rTensor_comm]; exact hx)
  have hw : g.lTensor K z = 0 := by
    apply hQinj
    rw [map_zero, ← lTensor_rTensor_comm, hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      hfg.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨u, rfl⟩ := ((lTensor_exact K hfg hg) z).1 hw
  have hx' : K.subtype.rTensor G u = x' := hFinj (by rw [lTensor_rTensor_comm, hz])
  rw [← hx', ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
    show ε ∘ₗ K.subtype = 0 from LinearMap.ext fun k ↦ k.2, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

/-- For an exact sequence `0 → G → N → Q → 0` with `Q` flat, `L ⊗ G → L ⊗ N` is injective for
every module `L`. -/
theorem lTensor_injective_of_flat_cokernel {G Q : Type*} [AddCommGroup G] [Module R G]
    [AddCommGroup Q] [Module R Q] [Module.Flat R Q] {f : G →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (L : Type*) [AddCommGroup L] [Module R L] : Function.Injective (f.lTensor L) :=
  lTensor_injective_of_flat_cokernel_aux hf hfg hg (Finsupp.linearCombination R (id : L → L))
    fun l ↦ ⟨Finsupp.single l 1, by simp⟩

/-- In an exact sequence `0 → G → N → Q → 0` with `N` and `Q` flat, `G` is flat. -/
theorem flat_of_flat_of_flat_cokernel {G Q : Type*} [AddCommGroup G] [Module R G]
    [AddCommGroup Q] [Module R Q] [Module.Flat R N] [Module.Flat R Q] {f : G →ₗ[R] N}
    {g : N →ₗ[R] Q} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Module.Flat R G := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have h : (f.lTensor R) ∘ₗ I.subtype.rTensor G = I.subtype.rTensor N ∘ₗ f.lTensor I := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hinj : Function.Injective ((f.lTensor R) ∘ₗ I.subtype.rTensor G) := by
    rw [h]
    exact (Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.injective_subtype).comp
      (lTensor_injective_of_flat_cokernel hf hfg hg I)
  rw [LinearMap.coe_comp] at hinj
  exact hinj.of_comp

end Purity

end Grothendieck.Folder127
