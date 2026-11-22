module

public import Grothendieck.Folder22CohenAlgebras
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 22, pages 15 to 17: uniqueness of formally smooth lifts (3.10, 3.12)

The typescript of folder 22 (`transcripts/22/22.modern.tex`, pages 15–17) states, with the
existence of a formally smooth flat lift `B` of a special fibre `B_0` (Cor. 3.10, and its case
`B_0 = K` a separable extension of `k`, the « Cohen ring » of Cor. 3.12), that such a lift is
*unique up to isomorphism*, and in 3.12 that, when `𝔪_B = 𝔪_A B`, `B` is formally smooth over `A`
if and only if it is flat with `K/k` separable. The existence halves are
`Grothendieck.Folder22CohenAlgebras.corollaire3_10` and `corollaire3_12_existence`; this file
proves the uniqueness halves and the equivalence 1) ⇔ 2) of 3.12.

The finding: uniqueness needs less than the page assumes. Only the source `B` has to be formally
smooth and only the target `B'` flat; the base `A` need be neither complete nor noetherian; and
the isomorphism can be chosen to induce the given one on special fibres.

Formal smoothness is `RingHom.FormallySmoothNAdic f 𝔪_B` (Stacks 07NI, 07EC (2)(b)), as in
`Grothendieck/Folder22CohenAlgebras.lean`.

**What is proved.**
* `exists_algHom_lift`: let `A` be a local ring, `B` a noetherian local `A`-algebra (local
  structure map) formally smooth over `A` for its `𝔪_B`-adic topology, `B'` a complete noetherian
  local `A`-algebra, and `e₀ : k ⊗_A B ≃ k ⊗_A B'` an isomorphism of special fibres. There is an
  `A`-algebra map `φ : B → B'` with `e₀ (1 ⊗ b) = 1 ⊗ φ(b)`.
* `bijective_of_lift`: if moreover `B` is complete and `B'` flat over `A`, every such `φ` is
  bijective.
* `corollaire3_10_uniqueness`: hence `B ≃ B'` as `A`-algebras, by an isomorphism lifting `e₀`:
  the uniqueness half of 3.10 (EGA 0_IV 19.7.2; Stacks 07NR is the existence).
* `corollaire3_12_uniqueness`: the uniqueness half of 3.12. Two complete noetherian local
  `A`-algebras, flat and formally smooth, whose special fibres are both identified with the same
  `k`-algebra `K`, are isomorphic over `A`, compatibly with the identifications.
* `corollaire3_12`: 1) ⇔ 2) of 3.12. For a local homomorphism `f : A → B` of noetherian local
  rings with `𝔪_B = 𝔪_A B`, `f` is formally smooth for the `𝔪_B`-adic topology if and only if `B`
  is flat over `A` and `k(B)/k(A)` is separable (`Algebra.IsSeparableExtension`).

**How.** Put `J = 𝔪_A B'`, so that `B'/J ≅ k ⊗_A B'`, and let `ψ : B → B'/J` be
`B → k ⊗_A B ≅ k ⊗_A B' ≅ B'/J`, which is surjective. Formal smoothness lifts `ψ` to
`φ : B → B'`: `J` is closed in the complete `𝔪_{B'}`-adic ring `B'`, and Stacks'
`exists_continuous_lift_of_isFormallySmooth_of_isAdic` performs the page's step-by-step lifting
along `B'/J^{n+1} → B'/J^n` and the passage to the limit. `φ` is surjective because it is
surjective modulo `J = (𝔪_A B) B'`, `B` is `𝔪_A B`-adically complete and `B'` is Hausdorff
(`surjective_of_mk_map_comp_surjective`). `φ` is injective by the local flatness criterion
(Stacks 00MK, EGA III 4.6.7.1, as Stacks'
`injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing`): `B'` is
flat over `A`, `B` is finite over itself, and `φ` is injective modulo `𝔪_A` because `e₀` is.
This is the local flatness argument of the page, not Nakayama on the graded pieces.
For 3.12, `corollaire3_9` reduces formal smoothness to that of the special fibre over `k`. When
`𝔪_B = 𝔪_A B` the special fibre is the residue field `K` of `B` (`specialFiberEquivResidueField`),
whose maximal ideal is `⊥`. Formal smoothness for the `⊥`-adic topology is mathlib's
`Algebra.FormallySmooth` (`formallySmoothNAdic_bot_iff`), which for a field extension is
separability (`Algebra.FormallySmooth.iff_isSeparableExtension`, EGA 0_IV 19.6.1).
The three topological helpers and the lifting lemma are adapted from private lemmas of
AxiomMath/Stacks (Apache-2.0), `StacksFrontier/RingTheory/GeometricallyRegular/
FormalSmoothness.lean`, which that module does not export.

**Not formalised.**
* Uniqueness of the isomorphism itself: `φ` is not unique (a Cohen ring has automorphisms inducing
  the identity on `K`), and the page does not claim it.
* As in `Folder22CohenAlgebras`, Cohen algebras and condition P (Déf. 3.7, Lemme 3.2,
  Théorème 3.6, Cor. 3.8, 3.11).
-/

open IsLocalRing
open scoped TensorProduct
open Module

universe u v

namespace Grothendieck.Folder22Uniqueness

/-- Every ideal of a noetherian local ring is closed for the `𝔪`-adic topology (Krull). Adapted
from Stacks' private `ideal_isClosed_maximal_adic`. -/
private theorem ideal_isClosed_maximal_adic
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (K : Ideal R) :
    letI : TopologicalSpace R := (maximalIdeal R).adicTopology
    IsClosed (K : Set R) := by
  let : TopologicalSpace R := (maximalIdeal R).adicTopology
  have hhaus : IsHausdorff (maximalIdeal R) (R ⧸ K) := inferInstance
  apply isClosed_of_closure_subset
  intro x hx
  have hxq : ∀ n, (K.mkQ x) ≡ 0
      [SMOD (maximalIdeal R) ^ n • (⊤ : Submodule R (R ⧸ K))] := by
    intro n
    obtain ⟨y, hy, z, hz, rfl⟩ :=
      (mem_closure_iff_nhds_basis
        ((maximalIdeal R).hasBasis_nhds_adic x)).mp hx n trivial
    rw [SModEq.zero]
    have hz' : z ∈ (maximalIdeal R) ^ n • (⊤ : Submodule R R) := by
      simpa [Ideal.smul_top_eq_map] using hz
    have hzq : K.mkQ z ∈ Submodule.map K.mkQ
        ((maximalIdeal R) ^ n • (⊤ : Submodule R R)) :=
      Submodule.mem_map_of_mem hz'
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hzq
    have hsum : K.mkQ x + K.mkQ z = 0 := by
      change K.mkQ (x + z) = 0
      exact (Submodule.Quotient.mk_eq_zero K).mpr hy
    have hxneg : K.mkQ x = -(K.mkQ z) := eq_neg_of_add_eq_zero_left hsum
    rw [hxneg]
    exact Submodule.neg_mem _ hzq
  exact (Submodule.Quotient.mk_eq_zero K).mp (hhaus.haus' (K.mkQ x) hxq)

/-- The quotient topology of an adic ring is adic for the image ideal. Adapted from Stacks'
private `quotient_isAdic_map`. -/
private theorem quotient_isAdic_map {R : Type*} [CommRing R] (I K : Ideal R) :
    letI : TopologicalSpace R := I.adicTopology
    IsAdic (I.map (Ideal.Quotient.mk K)) := by
  let : TopologicalSpace R := I.adicTopology
  have : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  have : IsTopologicalRing (R ⧸ K) := inferInstance
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [← Ideal.map_pow]
    rw [Ideal.map_eq_image_of_surjective (Ideal.Quotient.mk K)
      Ideal.Quotient.mk_surjective]
    exact QuotientRing.isOpenMap_coe K ((I ^ n : Ideal R) : Set R)
      (I.openAddSubgroup n).isOpen'
  · intro U hU
    change U ∈ nhds (Ideal.Quotient.mk K (0 : R)) at hU
    have hpre : (Ideal.Quotient.mk K) ⁻¹' U ∈ nhds (0 : R) :=
      continuous_quot_mk.continuousAt.tendsto hU
    obtain ⟨n, _, hn⟩ := I.hasBasis_nhds_zero_adic.mem_iff.mp hpre
    refine ⟨n, ?_⟩
    intro y hy
    rw [← Ideal.map_pow] at hy
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective).mp hy
    exact hn hx

/-- A local map to a quotient `S/K`, `K ≤ 𝔪_S`, is continuous for the `𝔪`-adic topology of the
source and the quotient of the `𝔪_S`-adic topology. Adapted from Stacks' private
`continuous_quotient_maximal_adic_of_localHom`. -/
private theorem continuous_quotient_maximal_adic_of_localHom
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (K : Ideal S) (hK : K ≤ maximalIdeal S) (f : R →+* S ⧸ K) [IsLocalHom f] :
    letI : TopologicalSpace S := (maximalIdeal S).adicTopology
    @Continuous R (S ⧸ K) (maximalIdeal R).adicTopology
      (inferInstance : TopologicalSpace (S ⧸ K)) f := by
  have hproper : K ≠ ⊤ := (hK.trans_lt (maximalIdeal.isMaximal S).lt_top).ne
  have : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing (S ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  let : TopologicalSpace S := (maximalIdeal S).adicTopology
  have htop := quotient_isAdic_map (maximalIdeal S) K
  have hmax : (maximalIdeal S).map (Ideal.Quotient.mk K) = maximalIdeal (S ⧸ K) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk K)
      Ideal.Quotient.mk_surjective
  rw [hmax] at htop
  change (inferInstance : TopologicalSpace (S ⧸ K)) =
    (maximalIdeal (S ⧸ K)).adicTopology at htop
  rw [htop]
  apply (RingHom.continuous_adic_iff _ _ _).mpr
  refine ⟨1, le_rfl, ?_⟩
  simpa only [pow_one] using (show ∀ x ∈ maximalIdeal R, f x ∈ maximalIdeal (S ⧸ K) from
    fun x hx => map_maximalIdeal_le f (Ideal.mem_map_of_mem f hx))

/-- A surjective map onto a quotient `T/J`, `J ≤ 𝔪_T`, of a complete noetherian local ring lifts
along a map formally smooth for the `𝔪`-adic topology. Adapted from Stacks' private
`exists_local_lift_of_formallySmoothNAdic`. -/
private theorem exists_lift {R : Type*} {S : Type*} {T : Type v}
    [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing T] [IsNoetherianRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (f : R →+* S) (h : RingHom.FormallySmoothNAdic.{v} f (maximalIdeal S))
    (a : R →+* T) (J : Ideal T) (hJ : J ≤ maximalIdeal T)
    (ψ : S →+* T ⧸ J) (hψ : Function.Surjective ψ)
    (hc : ψ.comp f = (Ideal.Quotient.mk J).comp a) :
    ∃ b : S →+* T, b.comp f = a ∧ (Ideal.Quotient.mk J).comp b = ψ := by
  have hproper : J ≠ ⊤ := (hJ.trans_lt (maximalIdeal.isMaximal T).lt_top).ne
  have : Nontrivial (T ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing (T ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsLocalHom ψ := hψ.isLocalHom
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  let : TopologicalSpace S := (maximalIdeal S).adicTopology
  have : IsTopologicalRing S := (maximalIdeal S).ringFilterBasis.isTopologicalRing
  have : IsLinearTopology S S := (maximalIdeal S).isLinearTopology
  let : TopologicalSpace T := (maximalIdeal T).adicTopology
  have : IsTopologicalRing T := (maximalIdeal T).ringFilterBasis.isTopologicalRing
  obtain ⟨b, _, hb, hbψ⟩ :=
    exists_continuous_lift_of_isFormallySmooth_of_isAdic
      f (maximalIdeal S) rfl
      ((isFormallySmooth_iff_formallySmoothNAdic f (maximalIdeal S) rfl).mpr h)
      (maximalIdeal T) rfl J (ideal_isClosed_maximal_adic J)
      1 (le_refl 1) (by simpa only [pow_one] using hJ)
      a continuous_of_discreteTopology ψ
      (continuous_quotient_maximal_adic_of_localHom J hJ ψ) hc
  exact ⟨b, hb, hbψ⟩

section Lift

variable {A : Type u} {B B' : Type v} [CommRing A] [IsLocalRing A]
  [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
  [CommRing B'] [IsNoetherianRing B'] [IsLocalRing B'] [IsAdicComplete (maximalIdeal B') B']
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra A B'] [IsLocalHom (algebraMap A B')]

/-- The map `B → k ⊗_A B ≅ k ⊗_A B' ≅ B' / 𝔪_A B'` built from an isomorphism of special
fibres. -/
noncomputable def specialFiberMap
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B') :
    B →+* B' ⧸ (maximalIdeal A).map (algebraMap A B') :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' (maximalIdeal A)).symm.toRingHom.comp
    (e₀.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := A) (A := ResidueField A) (B := B)).toRingHom)

omit [IsNoetherianRing B] [IsLocalRing B] [IsNoetherianRing B'] [IsLocalRing B']
  [IsAdicComplete (maximalIdeal B') B'] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A B')] in
theorem quotIdealMapEquivQuotTensor_specialFiberMap
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B') (b : B) :
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' (maximalIdeal A)
      (specialFiberMap e₀ b) = e₀ (1 ⊗ₜ b) :=
  AlgEquiv.apply_symm_apply _ _

omit [IsNoetherianRing B] [IsLocalRing B] [IsNoetherianRing B'] [IsLocalRing B']
  [IsAdicComplete (maximalIdeal B') B'] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A B')] in
theorem specialFiberMap_surjective
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B') :
    Function.Surjective (specialFiberMap e₀) := by
  intro y
  obtain ⟨z, hz⟩ :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' (maximalIdeal A)).symm.surjective y
  obtain ⟨w, rfl⟩ := e₀.surjective z
  obtain ⟨b, rfl⟩ := Algebra.TensorProduct.includeRight_surjective B residue_surjective w
  exact ⟨b, hz⟩

omit [IsNoetherianRing B] [IsLocalRing B] [IsNoetherianRing B'] [IsLocalRing B']
  [IsAdicComplete (maximalIdeal B') B'] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A B')] in
theorem specialFiberMap_algebraMap
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B') (r : A) :
    specialFiberMap e₀ (algebraMap A B r) = Ideal.Quotient.mk _ (algebraMap A B' r) := by
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' (maximalIdeal A)).injective
  rw [quotIdealMapEquivQuotTensor_specialFiberMap]
  have h (C : Type v) [CommRing C] [Algebra A C] :
      (1 : ResidueField A) ⊗ₜ[A] algebraMap A C r =
        algebraMap (ResidueField A) (ResidueField A ⊗[A] C) (residue A r) := by
    rw [← Algebra.TensorProduct.algebraMap_apply',
      IsScalarTower.algebraMap_apply A (ResidueField A) (ResidueField A ⊗[A] C)]
    rfl
  exact ((congrArg e₀ (h B)).trans (e₀.commutes _)).trans (h B').symm

omit [IsNoetherianRing B] [IsLocalRing B] [IsNoetherianRing B'] [IsLocalRing B']
  [IsAdicComplete (maximalIdeal B') B'] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A B')] in
/-- A map lifting `e₀` reduces to `specialFiberMap e₀` modulo `𝔪_A B'`. -/
theorem mk_eq_specialFiberMap
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B')
    (φ : B →ₐ[A] B') (hφ : ∀ b : B, e₀ (1 ⊗ₜ b) = 1 ⊗ₜ φ b) (b : B) :
    Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B')) (φ b) = specialFiberMap e₀ b := by
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' (maximalIdeal A)).injective
  rw [quotIdealMapEquivQuotTensor_specialFiberMap, hφ]
  rfl

omit [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] in
/-- **Existence of the comparison map.** If `B` is formally smooth over `A` for its `𝔪_B`-adic
topology and `B'` is complete, every isomorphism `e₀` of special fibres lifts to an `A`-algebra
map `φ : B → B'`. -/
@[montpellier "22, 15–17"]
theorem exists_algHom_lift
    (hB : RingHom.FormallySmoothNAdic.{v} (algebraMap A B) (maximalIdeal B))
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B') :
    ∃ φ : B →ₐ[A] B', ∀ b : B, e₀ (1 ⊗ₜ b) = 1 ⊗ₜ φ b := by
  obtain ⟨b, hb, hbψ⟩ := exists_lift (algebraMap A B) hB (algebraMap A B')
    ((maximalIdeal A).map (algebraMap A B')) (map_maximalIdeal_le _) (specialFiberMap e₀)
    (specialFiberMap_surjective e₀) (RingHom.ext fun r => specialFiberMap_algebraMap e₀ r)
  refine ⟨{ b with commutes' := fun r => DFunLike.congr_fun hb r }, fun x => ?_⟩
  rw [← quotIdealMapEquivQuotTensor_specialFiberMap, ← DFunLike.congr_fun hbψ x]
  rfl

omit [IsAdicComplete (maximalIdeal B') B'] in
/-- **The comparison map is an isomorphism.** If `B` is complete and `B'` flat over `A`, an
`A`-algebra map `φ : B → B'` lifting an isomorphism of special fibres is bijective: surjective by
completeness of `B`, injective by the local flatness criterion. -/
@[montpellier "22, 15–17"]
theorem bijective_of_lift [IsAdicComplete (maximalIdeal B) B] [Module.Flat A B']
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B')
    (φ : B →ₐ[A] B') (hφ : ∀ b : B, e₀ (1 ⊗ₜ b) = 1 ⊗ₜ φ b) :
    Function.Bijective φ := by
  set J := (maximalIdeal A).map (algebraMap A B')
  set I := (maximalIdeal A).map (algebraMap A B)
  have hmem (s : B) (hs : φ s ∈ J) : s ∈ I := by
    have h1 : specialFiberMap e₀ s = 0 := by
      rw [← mk_eq_specialFiberMap e₀ φ hφ]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hs
    have h2 : e₀ (1 ⊗ₜ s) = 0 := by
      rw [← quotIdealMapEquivQuotTensor_specialFiberMap, h1]
      exact map_zero _
    have h3 : Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)
        (Ideal.Quotient.mk I s) = 0 := by
      rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
      exact (map_eq_zero_iff e₀ e₀.injective).mp h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((map_eq_zero_iff _ (AlgEquiv.injective _)).mp h3)
  constructor
  · refine
      (Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := B) φ.toLinearMap ?_).1
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ z
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hs : φ s ∈ maximalIdeal A • (⊤ : Submodule A B') :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    have hqs : φ s ∈ J := by
      rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map]
      exact hs
    have hh := hmem s hqs
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at hh
    exact hh
  · have hmap : I.map (φ : B →+* B') = J := by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun r => φ.commutes r
    have : IsAdicComplete I B := isAdicComplete_of_le_of_fg_of_isAdicComplete
      (map_maximalIdeal_le _) ‹_› I.fg_of_isNoetherianRing
    have : IsHausdorff (I.map (φ : B →+* B')) B' := by
      rw [hmap]
      exact IsHausdorff.of_isLocalRing J B' (map_maximalIdeal_lt_top _).ne
    refine surjective_of_mk_map_comp_surjective (I := I) (φ : B →+* B') ?_
    rw [hmap]
    intro y
    obtain ⟨x, hx⟩ := specialFiberMap_surjective e₀ y
    exact ⟨x, (mk_eq_specialFiberMap e₀ φ hφ x).trans hx⟩

/-- **Corollaire 3.10, uniqueness.** Let `A` be a local ring, `B` and `B'` complete noetherian
local `A`-algebras (local structure maps), `B` formally smooth over `A` for its `𝔪_B`-adic
topology and `B'` flat over `A`. Every isomorphism `e₀ : k ⊗_A B ≃ k ⊗_A B'` of special fibres
lifts to an isomorphism `φ : B ≃ B'` of `A`-algebras. -/
@[montpellier "22, 15–17"]
theorem corollaire3_10_uniqueness [IsAdicComplete (maximalIdeal B) B] [Module.Flat A B']
    (hB : RingHom.FormallySmoothNAdic.{v} (algebraMap A B) (maximalIdeal B))
    (e₀ : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField A ⊗[A] B') :
    ∃ φ : B ≃ₐ[A] B', ∀ b : B, e₀ (1 ⊗ₜ b) = 1 ⊗ₜ φ b := by
  obtain ⟨φ, hφ⟩ := exists_algHom_lift hB e₀
  exact ⟨AlgEquiv.ofBijective φ (bijective_of_lift e₀ φ hφ), hφ⟩

/-- **Corollaire 3.12, uniqueness**: the Cohen ring of `K` over `A` is unique up to isomorphism.
Two complete noetherian local `A`-algebras `B`, `B'`, formally smooth and flat over `A`, whose
special fibres are both isomorphic to the same `k`-algebra `K`, are isomorphic as `A`-algebras
(by an isomorphism compatible with the two identifications of the special fibres). -/
@[montpellier "22, 15–17"]
theorem corollaire3_12_uniqueness {K : Type*} [CommRing K] [Algebra (ResidueField A) K]
    [IsAdicComplete (maximalIdeal B) B] [Module.Flat A B']
    (hB : RingHom.FormallySmoothNAdic.{v} (algebraMap A B) (maximalIdeal B))
    (e : ResidueField A ⊗[A] B ≃ₐ[ResidueField A] K)
    (e' : ResidueField A ⊗[A] B' ≃ₐ[ResidueField A] K) :
    ∃ φ : B ≃ₐ[A] B', ∀ b : B, e (1 ⊗ₜ b) = e' (1 ⊗ₜ φ b) := by
  obtain ⟨φ, hφ⟩ := corollaire3_10_uniqueness hB (e.trans e'.symm)
  refine ⟨φ, fun b => ?_⟩
  rw [← hφ b]
  exact (e'.apply_symm_apply _).symm

end Lift

section Separable

/-- Formal smoothness for the discrete (`⊥`-adic) topology is mathlib's `Algebra.FormallySmooth`
(square-zero lifting for all algebras). -/
theorem formallySmoothNAdic_bot_iff (R : Type u) (C : Type v) [CommRing R] [CommRing C]
    [Algebra R C] :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap R C) ⊥ ↔ Algebra.FormallySmooth R C := by
  constructor
  · intro h
    refine Algebra.FormallySmooth.of_comp_surjective fun T _ _ I hI g => ?_
    obtain ⟨γ, hγ, hγa⟩ := h T I hI (algebraMap R T) g.toRingHom
      (RingHom.ext fun r => g.commutes r) ⟨1, le_rfl, by simp⟩
    refine ⟨{ γ with commutes' := fun r => DFunLike.congr_fun hγa r }, ?_⟩
    ext x
    exact DFunLike.congr_fun hγ x
  · intro _ T _ J hJ f ψ hψ _
    let : Algebra R T := f.toAlgebra
    let ψ' : C →ₐ[R] T ⧸ J :=
      { ψ with commutes' := fun r ↦ RingHom.congr_fun hψ r }
    obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ ψ'
    refine ⟨g.toRingHom, congrArg AlgHom.toRingHom hg, ?_⟩
    ext r
    exact g.commutes r

/-- When `𝔪_B = 𝔪_A B`, the special fibre `k ⊗_A B` is the residue field of `B`, as a
`k`-algebra. -/
noncomputable def specialFiberEquivResidueField {A : Type u} {B : Type v} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (hm : letI : Algebra A B := f.toAlgebra; maximalIdeal B = (maximalIdeal A).map f) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
    (ResidueField A ⊗[A] B) ≃ₐ[ResidueField A] ResidueField B :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (maximalIdeal A)).symm.toRingEquiv.trans (Ideal.quotEquivOfEq hm.symm))
    (by
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      have h1 : algebraMap (ResidueField A) (ResidueField A ⊗[A] B) (residue A a) =
          (1 : ResidueField A) ⊗ₜ[A] f a := by
        change algebraMap (ResidueField A) _ (algebraMap A (ResidueField A) a) = _
        rw [← IsScalarTower.algebraMap_apply A (ResidueField A) (ResidueField A ⊗[A] B),
          Algebra.TensorProduct.algebraMap_apply']
        rfl
      rw [h1]
      have h2 : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).symm
          ((1 : ResidueField A) ⊗ₜ[A] f a) = Ideal.Quotient.mk _ (f a) :=
        (AlgEquiv.symm_apply_eq _).mpr rfl
      exact (congrArg (Ideal.quotEquivOfEq hm.symm) h2).trans rfl)

/-- **Corollaire 3.12, 1) ⇔ 2).** Let `f : A → B` be a local homomorphism of noetherian local
rings with `𝔪_B = 𝔪_A B`. Then `B` is formally smooth over `A` for the `𝔪_B`-adic topology if
and only if `B` is flat over `A` and the residue extension `K/k` is separable (in the sense of
`Algebra.IsSeparableExtension`: every finitely generated subextension separably generated). -/
@[montpellier "22, 15–17"]
theorem corollaire3_12 {A : Type u} {B : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (f : A →+* B)
    [IsLocalHom f]
    (hm : letI : Algebra A B := f.toAlgebra; maximalIdeal B = (maximalIdeal A).map f) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
    RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B) ↔
      Module.Flat A B ∧ Algebra.IsSeparableExtension (ResidueField A) (ResidueField B) := by
  let : Algebra A B := f.toAlgebra
  let : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
  refine (Grothendieck.Folder22CohenAlgebras.corollaire3_9 f).trans (and_congr_right fun _ => ?_)
  let E := specialFiberEquivResidueField f hm
  have hbot : maximalIdeal (ResidueField A ⊗[A] B) = ⊥ := by
    ext x
    refine ⟨fun hx => ?_, fun hx => (Ideal.mem_bot.mp hx) ▸ zero_mem _⟩
    have hE : ¬ IsUnit (E x) := fun hu => hx ((isUnit_map_iff E x).mp hu)
    rw [isUnit_iff_ne_zero, not_not] at hE
    exact Ideal.mem_bot.mpr ((map_eq_zero_iff E E.injective).mp hE)
  change RingHom.FormallySmoothNAdic.{max u v}
    (algebraMap (ResidueField A) (ResidueField A ⊗[A] B))
    (maximalIdeal (ResidueField A ⊗[A] B)) ↔ _
  rw [hbot, formallySmoothNAdic_bot_iff, ← Algebra.FormallySmooth.iff_isSeparableExtension]
  exact ⟨fun _ => .of_equiv E, fun _ => .of_equiv E.symm⟩

end Separable

end Grothendieck.Folder22Uniqueness

#print axioms Grothendieck.Folder22Uniqueness.exists_algHom_lift
#print axioms Grothendieck.Folder22Uniqueness.bijective_of_lift
#print axioms Grothendieck.Folder22Uniqueness.corollaire3_10_uniqueness
#print axioms Grothendieck.Folder22Uniqueness.corollaire3_12_uniqueness
#print axioms Grothendieck.Folder22Uniqueness.corollaire3_12
