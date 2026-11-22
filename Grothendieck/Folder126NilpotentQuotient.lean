module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.RingTheory.Flat.SquareZeroConormal
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 126, pages 4 to 7: deforming a flat equivalence relation across a nilpotent thickening

Finding `126-nilpotent-deformation-quotient`. Pages 4 to 7 prove, in the reading's completed
form: let `X₀ ⊂ X` be defined by a nilpotent ideal `𝒥_X`, `R ⇉ X` a flat equivalence relation
and `R₀ = R ×_X X₀`; if `R₀ ⇉ X₀` is effective, with `X₀ → Y₀` fpqc and quasi-separated and
`R₀ ≅ X₀ ×_{Y₀} X₀`, then `R` is effective, with quotient `Y` a nilpotent thickening of `Y₀`,
`X → Y` flat and `R ≅ X ×_Y X`. The proof reduces to `𝒥_X² = 0`, descends `𝒥_X` to a
quasi-coherent `𝒥_Y` on `Y₀` (`𝒥_X ≅ 𝒥_Y ⊗ 𝒪_{X₀}`), builds `𝒪_Y = Ker(𝒪_X ⇉ 𝒪_R)`, proves
`0 → 𝒥_Y → 𝒪_Y → 𝒪_{Y₀} → 0` exact by Čech vanishing (lift, then correct the lift), and ends
(page 7) with two steps: `X` is flat over `Y` by the flatness criterion for nilpotent
thickenings, and `R → X ×_Y X`, a morphism of flat `Y`-schemes that is an isomorphism modulo the
nilpotent ideal `𝒥_Y`, is an isomorphism.

This file formalises those two closing steps of page 7, in the affine case.

**What is proved.**
* `subsingleton_of_nilpotent_smul_top_eq_top`: Nakayama's lemma for a nilpotent ideal, with no
  finiteness: if `I ^ n = 0` and `I • Q = Q`, then `Q = 0`.
* `surjective_of_lTensor_quotient_nilpotent`: an `A`-linear map `u : M → N` which is surjective
  modulo a nilpotent ideal `I` (that is, `(A ⧸ I) ⊗ u` is surjective) is surjective.
* `bijective_of_lTensor_quotient_nilpotent_of_flat`: if moreover `N` is flat over `A` and
  `(A ⧸ I) ⊗ u` is bijective, then `u` is bijective. This is the statement the page uses at the
  end (« donc `R → P` est un isomorphisme »), which the reading calls classical: a morphism of
  flat `Y`-schemes that is an isomorphism modulo a nilpotent ideal of `Y` is an isomorphism. Only
  the target needs to be flat.
* `flat_and_bijective_of_thickening`: the affine form of page 7. Let `Y = Spec A'` with
  `I ⊂ A'`, `I² = 0` (the ideal `𝒥_Y`, `Y₀ = Spec (A' ⧸ I)`), `X = Spec B'` over `Y` with
  `X₀ = Spec B`, `B = B' ⧸ J`, `J² = 0` (the ideal `𝒥_X`), `X₀` flat over `Y₀`, and assume the
  canonical map `I ⊗_{A'} B → J` bijective, the affine form of `𝒥_Y 𝒪_X = 𝒥_X ≅ 𝒥_Y ⊗ 𝒪_{X₀}`.
  Let `R = Spec C'` be flat over `X` (via `B' → C'`) and `φ : B' ⊗_{A'} B' → C'` the
  `A'`-algebra map of `R → X ×_Y X`, bijective after `(A' ⧸ I) ⊗_{A'} -` (the reduction of
  `R → X ×_Y X` modulo `𝒥_Y`, which the page identifies with `R₀ ≅ X₀ ×_{Y₀} X₀`). Then `B'`
  is flat over `A'` (`X → Y` flat) and `φ` is bijective (`R ≅ X ×_Y X`).

**How.** Nakayama for a nilpotent ideal is the induction `Iᵏ • Q = Q`. Surjectivity: the cokernel
`Q` of `u` satisfies `(A ⧸ I) ⊗ Q = 0` by right exactness, that is `Q = I • Q`
(`TensorProduct.quotTensorEquivQuotSMul`). Injectivity: with `u` surjective and `N` flat, the
sequence `0 → (A ⧸ I) ⊗ Ker u → (A ⧸ I) ⊗ M → (A ⧸ I) ⊗ N` stays exact
(`LinearMap.lTensor_injective_of_exact_of_flat`), so `(A ⧸ I) ⊗ Ker u = 0` and `Ker u = 0`.
Flatness of `B'` over `A'` is Stacks 063Y in the affine case,
`Ideal.bijective_fibreTensorSMulHomToKer_iff` (in the vendored Stacks files, through Stacks 051C,
the Tor criterion for flatness across a nilpotent ideal), and flatness of `C'` over `A'` is
`Module.Flat.trans`. The draft pointed to Stacks 08VU, whose vendored form is stated for ringed
topoi; the affine statement used here is the module-level 063Y.

**Not formalised.**
* The scheme-level statement: effectivity of `R`, the construction of `Y` as the ringed space
  `(Y₀, Ker(𝒪_X ⇉ 𝒪_R))` and the gluing of its affine pieces into a scheme, the reduction from a
  nilpotent `𝒥_X` to `𝒥_X² = 0`, and the identification `R₀ = R ×_X X₀`.
* Here `A'` and `φ` are given and the descent of `𝒥_X` is the hypothesis that `I ⊗_{A'} B → J`
  is bijective. `Folder126NilpotentDescent` removes that hypothesis in the affine case: it
  constructs `A' = Ker(B' ⇉ C')`, proves `0 → 𝒥_Y → 𝒪_Y → 𝒪_{Y₀} → 0` exact (lifting an
  invariant function and correcting the lift with the degree-one exactness of the concrete
  Amitsur complex, Stacks 023M, available in the vendored files as
  `Module.Descent.exact_amitsur_degree_one`), and derives the bijectivity by descent
  (Stacks 023N). The vanishing `Ȟ⁰(X₀/Y₀, ℋ¹(𝒥_Y)) = 0` of Remark 2 (page 3) for fpqc
  quasi-separated covers of a non-affine `Y₀` remains open, with the other points listed there.
-/

namespace Grothendieck.Folder126NilpotentQuotient

open TensorProduct

universe u

section Nakayama

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Nakayama's lemma for a nilpotent ideal, without finiteness: if `I ^ n = 0` and `I • Q = Q`
then `Q = 0`. -/
theorem subsingleton_of_nilpotent_smul_top_eq_top (n : ℕ) (hn : I ^ n = ⊥)
    {Q : Type*} [AddCommGroup Q] [Module A Q] (h : I • (⊤ : Submodule A Q) = ⊤) :
    Subsingleton Q := by
  have key : ∀ k : ℕ, (I ^ k) • (⊤ : Submodule A Q) = ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih => rw [pow_succ, ← smul_smul, h, ih]
  have hz : ∀ q : Q, q = 0 := by
    intro q
    have hq : q ∈ (I ^ n) • (⊤ : Submodule A Q) := by
      rw [key n]
      exact Submodule.mem_top
    rw [hn] at hq
    refine Submodule.smul_induction_on hq ?_ ?_
    · intro r hr m _
      rw [Ideal.mem_bot] at hr
      rw [hr, zero_smul]
    · intro x y hx hy
      rw [hx, hy, add_zero]
  refine ⟨fun a b => ?_⟩
  rw [hz a, hz b]

/-- If `(A ⧸ I) ⊗ Q = 0` then `I • Q = Q`. -/
theorem smul_top_eq_top_of_subsingleton_lTensor {Q : Type*} [AddCommGroup Q] [Module A Q]
    (h : Subsingleton ((A ⧸ I) ⊗[A] Q)) : I • (⊤ : Submodule A Q) = ⊤ := by
  have hq : Subsingleton (Q ⧸ (I • (⊤ : Submodule A Q))) :=
    (TensorProduct.quotTensorEquivQuotSMul Q I).symm.toEquiv.subsingleton
  exact Submodule.Quotient.subsingleton_iff.mp hq

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- A linear map which is surjective modulo a nilpotent ideal is surjective. -/
@[montpellier "126, 7"]
theorem surjective_of_lTensor_quotient_nilpotent (n : ℕ) (hn : I ^ n = ⊥) (u : M →ₗ[A] N)
    (hu : Function.Surjective (LinearMap.lTensor (A ⧸ I) u)) : Function.Surjective u := by
  have hex := lTensor_exact (A ⧸ I) (LinearMap.exact_map_mkQ_range u)
    (Submodule.mkQ_surjective (LinearMap.range u))
  have hQ : Subsingleton ((A ⧸ I) ⊗[A] (N ⧸ LinearMap.range u)) := by
    have hz : ∀ z : (A ⧸ I) ⊗[A] (N ⧸ LinearMap.range u), z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (A ⧸ I)
        (Submodule.mkQ_surjective (LinearMap.range u)) z
      obtain ⟨v, rfl⟩ := hu w
      exact hex.apply_apply_eq_zero v
    refine ⟨fun a b => ?_⟩
    rw [hz a, hz b]
  have htop := smul_top_eq_top_of_subsingleton_lTensor I hQ
  have hsub : Subsingleton (N ⧸ LinearMap.range u) :=
    subsingleton_of_nilpotent_smul_top_eq_top I n hn htop
  exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hsub)

/-- **Page 7, the last step.** A linear map `u : M → N` into a flat module which is bijective
modulo a nilpotent ideal `I` (that is, `(A ⧸ I) ⊗ u` is bijective) is bijective. -/
@[montpellier "126, 7"]
theorem bijective_of_lTensor_quotient_nilpotent_of_flat [Module.Flat A N] (n : ℕ)
    (hn : I ^ n = ⊥) (u : M →ₗ[A] N)
    (hu : Function.Bijective (LinearMap.lTensor (A ⧸ I) u)) : Function.Bijective u := by
  have hsurj : Function.Surjective u := surjective_of_lTensor_quotient_nilpotent I n hn u hu.2
  have hex := LinearMap.exact_subtype_ker_map u
  have hinj : Function.Injective (LinearMap.lTensor (A ⧸ I) (LinearMap.ker u).subtype) :=
    LinearMap.lTensor_injective_of_exact_of_flat u hsurj (LinearMap.ker u).subtype
      (LinearMap.ker u).injective_subtype hex (A ⧸ I)
  have hex' := lTensor_exact (A ⧸ I) hex hsurj
  have hK : Subsingleton ((A ⧸ I) ⊗[A] LinearMap.ker u) := by
    have hz : ∀ z : (A ⧸ I) ⊗[A] LinearMap.ker u, z = 0 := by
      intro z
      apply hinj
      apply hu.1
      simp only [map_zero]
      exact hex'.apply_apply_eq_zero z
    refine ⟨fun a b => ?_⟩
    rw [hz a, hz b]
  have htop := smul_top_eq_top_of_subsingleton_lTensor I hK
  have hsub : Subsingleton (LinearMap.ker u) :=
    subsingleton_of_nilpotent_smul_top_eq_top I n hn htop
  refine ⟨(injective_iff_map_eq_zero u).mpr fun m hm => ?_, hsurj⟩
  have h0 : (⟨m, LinearMap.mem_ker.mpr hm⟩ : LinearMap.ker u) = 0 := Subsingleton.elim _ _
  have h1 := congrArg Subtype.val h0
  exact h1

end Nakayama

section Thickening

variable {A' : Type u} [CommRing A'] (I : Ideal A')
  {B' : Type u} [CommRing B'] [Algebra A' B']
  {B : Type u} [CommRing B] [Algebra A' B] [Algebra B' B] [Algebra (A' ⧸ I) B]
  [IsScalarTower A' B' B] [IsScalarTower A' (A' ⧸ I) B]
  {C' : Type u} [CommRing C'] [Algebra A' C'] [Algebra B' C'] [IsScalarTower A' B' C']

/-- **Page 7, affine case.** Let `I ⊂ A'` with `I² = 0` (the ideal of `Y₀ ⊂ Y`), `B = B' ⧸ J`
with `J² = 0` (the ideal of `X₀ ⊂ X`), `B` flat over `A' ⧸ I`, and the canonical map
`I ⊗_{A'} B → J` bijective (`𝒥_Y 𝒪_X = 𝒥_X ≅ 𝒥_Y ⊗ 𝒪_{X₀}`). Let `C'` be flat over `B'`
(`R → X` flat) and `φ : B' ⊗_{A'} B' → C'` an `A'`-algebra map (`R → X ×_Y X`) whose reduction
`(A' ⧸ I) ⊗ φ` is bijective. Then `B'` is flat over `A'` (`X → Y` is flat) and `φ` is bijective
(`R ≅ X ×_Y X`). -/
@[montpellier "126, 7"]
theorem flat_and_bijective_of_thickening (hI2 : I ^ 2 = ⊥)
    (hJ2 : RingHom.ker (algebraMap B' B) ^ 2 = ⊥)
    (hsurj : Function.Surjective (algebraMap B' B)) (hflat : Module.Flat (A' ⧸ I) B)
    (hJ : Function.Bijective (I.fibreTensorSMulHomToKer B' B hJ2 hsurj))
    [Module.Flat B' C'] (φ : B' ⊗[A'] B' →ₐ[A'] C')
    (hφ : Function.Bijective (LinearMap.lTensor (A' ⧸ I) φ.toLinearMap)) :
    Module.Flat A' B' ∧ Function.Bijective φ := by
  have hB' : Module.Flat A' B' :=
    ((I.bijective_fibreTensorSMulHomToKer_iff B' B hI2 hJ2 hsurj hflat).mp hJ).1
  have hC' : Module.Flat A' C' := Module.Flat.trans A' B' C'
  have h := bijective_of_lTensor_quotient_nilpotent_of_flat I 2 hI2 φ.toLinearMap hφ
  rw [AlgHom.coe_toLinearMap] at h
  exact ⟨hB', h⟩

end Thickening

end Grothendieck.Folder126NilpotentQuotient
