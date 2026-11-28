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
# Folder 127, pages 2–4, 15, 19: the closure of a flat quotient, what is within reach

Finding `127-closure-flatness-artinian-or-trait`. For `X → Y`, `F` coherent on `X` and a quotient
`G_U` of `F|_U` flat over `Y`, the page's « Vrai théorème » (p. 15) says that, when the local
rings of `X` at the points of `X − U` have geometrically normal formal fibres, the closure
`G = Im(F → i_*G_U)` is flat over `Y` with `U` universally `G`-dense relative to `Y` if and only
if this holds after every base change `Y' → Y` with `Y'` artinian or a trait. The affine statement
is `OpenProblems.Findings.Folder127.ClosureFlatnessArtinianOrTrait`.

**That statement is not proved here.** Its converse implication (from the artinian and trait base
changes back to `Y`) needs EGA IV 11.8 and 11.10, which are in neither Mathlib nor the Stacks
library, and is the only place where the formal fibres are used. This file proves the parts of it
that are commutative algebra, in the notation of the statement: `φ : M → N` with `N` flat over the
base, `G` the image of `φ`.

## Main results

* `IsFlatClosureSolution.baseChange`: the direct implication of the criterion, for every base
  change `A → A'` and with no hypothesis: if `G` is flat with `G → N` universally injective, so is
  the image of `A' ⊗ M → A' ⊗ N` over `A'`.
* `flat_range_of_isDedekindDomain`: over a Dedekind domain (so over a trait) the image `G` is
  always flat: the flatness half of the condition is automatic there.
* `isFlatClosureSolution_iff_of_isDedekindDomain`: over a Dedekind domain, the condition is that
  `G` be saturated in `N` (`r n ∈ G` with `r ≠ 0` implies `n ∈ G`). So the condition of the
  criterion over a trait `Y'` is only the density clause, and it is a saturation.
* `isLocalizedModule_range_subtype`, `IsAffineSetting.isLocalizedModule_range`: over any base, the
  closure restricts to `G_U` on `U`: `N` is the localisation of `G` at `g`.
* `ker_eq_of_isTorsionFree_quotient`: uniqueness over a domain when `U` is the generic fibre: a
  quotient of `M` that is torsion-free and has the generic fibre of `G` is `G`.
* `not_flat_range_zmodFour`: over the artinian ring `ℤ/4`, the closure of a flat quotient need not
  be flat: the image of `(a, b) ↦ a + 2 T⁻¹ b` from `(ℤ/4)[X]²` to `(ℤ/4)[T, T⁻¹]`, in the setting
  `IsAffineSetting` with `g = X`. So over an artinian base the flatness half is a condition.

## Implementation notes

For the base change, `A' ⊗ G → A' ⊗ N` is injective by hypothesis, so the image `G'` of
`A' ⊗ M` is `A' ⊗ G` (`range_baseChange`), flat over `A'`, and
`A'' ⊗_{A'} G' = A'' ⊗_A G → A'' ⊗_A N` is injective by the same hypothesis. Over a Dedekind
domain, flat is torsion-free (Mathlib), which gives the flatness of `G ⊆ N` and, for `N/G`, the
equivalence with saturation; `G → N` is universally injective when `N/G` is flat, and conversely
its injectivity modulo `r` gives `G ∩ r N = r G` (`inf_smul_top_le_of_injective_baseChange`).
The counterexample is `2 T⁻¹ ∈ G`, killed by `2` and not in `2 G`, against the equational
criterion of flatness; `k[ε]` in place of `ℤ/4`, with `ε` for `2`, gives the same.

## Not formalised

* The converse implication of the criterion, and with it the role of the formal fibres.
* Anything for a non-affine `X` or a retrocompact open that is not principal.

## References

* A. Grothendieck, folder 127, pp. 2–4, 15, 19 (finding `127-closure-flatness-artinian-or-trait`)
* [EGA IV] 11.8, 11.10
-/

@[expose] public section

open TensorProduct Polynomial LaurentPolynomial OpenProblems.Findings.Folder127

universe u

namespace Grothendieck.Folder127

/-! ### The direct implication: base change -/

section BaseChange

variable {A M N : Type u} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The image of `A' ⊗ M → A' ⊗ N` is the image of `A' ⊗ G`, for `G` the image of `M → N`. -/
theorem range_baseChange (A' : Type*) [CommRing A'] [Algebra A A'] (φ : M →ₗ[A] N) :
    LinearMap.range (φ.baseChange A') =
      LinearMap.range ((LinearMap.range φ).subtype.baseChange A') := by
  conv_lhs => rw [← φ.subtype_comp_rangeRestrict, LinearMap.baseChange_comp]
  exact LinearMap.range_comp_of_range_eq_top _ <| LinearMap.range_eq_top.2 <|
    LinearMap.lTensor_surjective A' φ.surjective_rangeRestrict

/-- **The direct implication of the criterion of folder 127, p. 15, affine case.** If the image
`G` of `φ : M → N` is flat over `A` with `G → N` universally injective, the same holds over `A'`
for the image of `A' ⊗ M → A' ⊗ N`, for every `A → A'`: artinian, a trait or not. No hypothesis
on `M`, `N` or the formal fibres is used. The converse is not proved. -/
@[montpellier "127, 15"]
theorem IsFlatClosureSolution.baseChange {φ : M →ₗ[A] N} (h : IsFlatClosureSolution A φ)
    (A' : Type u) [CommRing A'] [Algebra A A'] : IsFlatClosureSolution A' (φ.baseChange A') := by
  have := h.1
  let e := LinearEquiv.ofInjective _ (h.2 A')
  rw [IsFlatClosureSolution, range_baseChange]
  refine ⟨.of_linearEquiv e.symm, fun A'' _ _ ↦ ?_⟩
  algebraize [(algebraMap A' A'').comp (algebraMap A A')]
  refine .of_comp_right (g := e.toLinearMap.baseChange A'') ?_
    (LinearMap.lTensor_surjective A'' e.surjective)
  rw [← LinearMap.coe_comp, ← LinearMap.baseChange_comp,
    show _ ∘ₗ e.toLinearMap = (LinearMap.range φ).subtype.baseChange A' from rfl,
    LinearMap.baseChange_baseChange]
  simpa using h.2 A''

end BaseChange

/-! ### Over a Dedekind domain: the trait -/

section Dedekind

variable {R M N : Type u} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Flat R N]

/-- **Over a trait the closure of a flat quotient is flat** (folder 127, pp. 2–4): over a Dedekind
domain `R`, the image of a map `φ : M → N` into a flat module is flat, being torsion-free. This
covers `N` a vector space over the fraction field (`U` the generic fibre) and `N` a module over a
localisation `B_g` of an `R`-algebra (`U = D(g)`). -/
@[montpellier "127, 2–4"]
theorem flat_range_of_isDedekindDomain (φ : M →ₗ[R] N) : Module.Flat R (LinearMap.range φ) :=
  inferInstance

/-- **The condition of the criterion over a trait** (folder 127, p. 15): over a Dedekind domain
`R` and for `N` flat, the image `G` of `φ : M → N` is flat with `G → N` universally injective if
and only if `G` is saturated in `N`. Flatness is automatic (`flat_range_of_isDedekindDomain`);
the saturation is the density of `U` in the fibres. -/
@[montpellier "127, 15"]
theorem isFlatClosureSolution_iff_of_isDedekindDomain (φ : M →ₗ[R] N) :
    IsFlatClosureSolution R φ ↔
      ∀ (r : R) (n : N), r ≠ 0 → r • n ∈ LinearMap.range φ → n ∈ LinearMap.range φ := by
  set G := LinearMap.range φ
  refine ⟨fun h r n hr hn ↦ ?_, fun h ↦ ⟨inferInstance, fun R' _ _ ↦ ?_⟩⟩
  · obtain ⟨g, hg, hgn⟩ := (Submodule.ideal_span_singleton_smul r G).le
      (inf_smul_top_le_of_injective_baseChange G _ (h.2 _)
        ⟨hn, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) trivial⟩)
    rwa [← smul_right_injective N hr hgn]
  · have : Module.IsTorsionFree R (N ⧸ G) := .of_smul_eq_zero fun r x hx ↦ by
      induction x using Submodule.Quotient.induction_on with | _ n
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      exact or_iff_not_imp_left.2 fun hr ↦ (Submodule.Quotient.mk_eq_zero _).2 (h r n hr hx)
    exact LinearMap.lTensor_injective_of_exact_of_flat _ G.mkQ_surjective _ G.injective_subtype
      (LinearMap.exact_subtype_mkQ G) R'

end Dedekind

/-! ### The closure extends the quotient, and is the only flat quotient that does -/

section Extension

/-- **The closure restricts to the given quotient on `U`.** Let `S` be a multiplicative subset of
`B` acting invertibly on `N`, and `φ : M → N` a `B`-linear map that is surjective after inverting
`S`. Then `N` is the localisation at `S` of the image of `φ`. No base ring and no flatness. -/
theorem isLocalizedModule_range_subtype {B M N : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (S : Submonoid B) (φ : M →ₗ[B] N)
    (hS : ∀ s : S, IsUnit (algebraMap B (Module.End B N) s))
    (hφ : ∀ n : N, ∃ s : S, s • n ∈ LinearMap.range φ) :
    IsLocalizedModule S (LinearMap.range φ).subtype where
  map_units := hS
  surj n := let ⟨s, hs⟩ := hφ n; ⟨(⟨s • n, hs⟩, s), rfl⟩
  exists_of_eq h := ⟨1, congrArg _ (Subtype.ext h)⟩

/-- In the affine setting of the finding (`U = D(g)`), the closure `G = Im(M → N)` restricts to
`G_U` on `U`: `N` is the localisation of `G` at `g`. -/
@[montpellier "127, 2–4"]
theorem IsAffineSetting.isLocalizedModule_range {A B M N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module A N] {φ : M →ₗ[B] N}
    {g : B} (h : IsAffineSetting A B M N φ g) :
    IsLocalizedModule (.powers g) (LinearMap.range φ).subtype :=
  isLocalizedModule_range_subtype _ φ (by rintro ⟨_, k, rfl⟩; simpa using h.2.2.1.pow k)
    fun n ↦ let ⟨m, k, hk⟩ := h.2.2.2.1 n; ⟨⟨g ^ k, k, rfl⟩, m, hk.symm⟩

/-- **Uniqueness over a domain, `U` the generic fibre** (folder 127, pp. 2–4). Let `φ : M → N`
with `N` torsion-free over the domain `R`. A submodule `P` of `M` with `M ⧸ P` torsion-free (flat,
when `R` is Dedekind) that agrees with `ker φ` at the generic point is `ker φ`: the image of `φ`
is the only torsion-free quotient of `M` with that generic fibre. -/
@[montpellier "127, 2–4"]
theorem ker_eq_of_isTorsionFree_quotient {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
    (φ : M →ₗ[R] N) (P : Submodule R M) [Module.IsTorsionFree R (M ⧸ P)]
    (h : ∀ m, (∃ r : R, r ≠ 0 ∧ r • m ∈ P) ↔ ∃ r : R, r ≠ 0 ∧ r • m ∈ LinearMap.ker φ) :
    P = LinearMap.ker φ := by
  ext m
  rw [← show (∃ r : R, r ≠ 0 ∧ r • m ∈ P) ↔ m ∈ P from ⟨fun ⟨r, hr, hm⟩ ↦ by
    rwa [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, smul_eq_zero_iff_right hr,
      Submodule.Quotient.mk_eq_zero] at hm, fun hm ↦ ⟨1, one_ne_zero, by simpa⟩⟩, h]
  exact ⟨fun ⟨r, hr, hm⟩ ↦ by simpa [hr] using hm, fun hm ↦ ⟨1, one_ne_zero, by simpa using hm⟩⟩

end Extension

/-! ### Over an artinian base the closure need not be flat -/

section Counterexample

/-- The map `(a, b) ↦ a + 2 T⁻¹ b` from `(ℤ/4)[X]²` to `(ℤ/4)[T, T⁻¹]`. -/
noncomputable def zmodFour : (ZMod 4)[X] × (ZMod 4)[X] →ₗ[(ZMod 4)[X]] (ZMod 4)[T;T⁻¹] :=
  (LinearMap.toSpanSingleton _ _ 1).coprod
    (LinearMap.toSpanSingleton _ _ (LaurentPolynomial.C 2 * T (-1)))

/-- **Over an artinian base the closure of a flat quotient need not be flat.** Over `A = ℤ/4`,
with `B = A[X]`, `g = X`, `M = B²` and `N = A[T, T⁻¹]` (free over `A`), the map `zmodFour` is in
the setting `IsAffineSetting` of the finding and its image is not flat over `A`: it contains
`2 T⁻¹`, which `2` kills and which is not twice an element of the image. Compare
`flat_range_of_isDedekindDomain`. -/
@[montpellier "127, 15"]
theorem not_flat_range_zmodFour :
    IsAffineSetting (ZMod 4) (ZMod 4)[X] ((ZMod 4)[X] × (ZMod 4)[X]) (ZMod 4)[T;T⁻¹] zmodFour X ∧
      ¬ Module.Flat (ZMod 4) (LinearMap.range (zmodFour.restrictScalars (ZMod 4))) := by
  refine ⟨⟨inferInstance, inferInstance, ?_, fun n ↦ ?_, inferInstance⟩, fun hflat ↦ ?_⟩
  · exact IsLocalizedModule.map_units (S := .powers X)
      (Algebra.linearMap (ZMod 4)[X] (ZMod 4)[T;T⁻¹]) ⟨X, Submonoid.mem_powers X⟩
  · obtain ⟨k, f, hf⟩ := n.exists_T_pow
    exact ⟨(f, 0), k, by simp [zmodFour, Algebra.smul_def, hf]⟩
  have h4 : (LaurentPolynomial.C 2 * LaurentPolynomial.C 2 : (ZMod 4)[T;T⁻¹]) = 0 := by
    rw [← map_mul, show (2 * 2 : ZMod 4) = 0 by decide, map_zero]
  let x : LinearMap.range (zmodFour.restrictScalars (ZMod 4)) :=
    ⟨LaurentPolynomial.C 2 * T (-1), (0, 1), by simp [zmodFour]⟩
  -- `2 x = 0`, so by the equational criterion `x = ∑ aⱼ yⱼ` with `2 aⱼ = 0`, that is `aⱼ = 2 bⱼ`.
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.iff_forall_isTrivialRelation.1 hflat (l := 1)
    (f := fun _ ↦ 2) (x := fun _ ↦ x)
    (Subtype.ext (by simp [x, LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, h4]))
  choose b hb using fun j ↦ (by decide : ∀ c : ZMod 4, 2 * c = 0 → ∃ b, c = 2 * b) (a 0 j)
    (by simpa using ha j)
  -- Hence `2 T⁻¹ = 2 (p + 2 T⁻¹ q) = 2 p`, and `2 = 2 p X` in `(ℤ/4)[X]`, false at `X = 0`.
  obtain ⟨⟨p, q⟩, hpq⟩ := (∑ j, b j • y j).2
  have h1 := congrArg Subtype.val (hy 0)
  rw [show (∑ j, a 0 j • y j) = (2 : ZMod 4) • ∑ j, b j • y j by
    simp [hb, mul_smul, Finset.smul_sum], Submodule.coe_smul, ← hpq,
    LaurentPolynomial.smul_eq_C_mul] at h1
  have h2 := congrArg (· * T 1) h1
  simp only [x, zmodFour, LinearMap.coe_restrictScalars, LinearMap.coprod_apply,
    LinearMap.toSpanSingleton_apply, Algebra.smul_def, algebraMap_eq_toLaurent, mul_one,
    mul_add, add_mul] at h2
  rw [show LaurentPolynomial.C 2 * (toLaurent q * (LaurentPolynomial.C 2 * T (-1))) * T 1 =
    toLaurent q * (LaurentPolynomial.C 2 * LaurentPolynomial.C 2) * (T (-1) * T 1) by ring, h4,
    mul_zero, zero_mul, add_zero, mul_assoc, ← T_add] at h2
  exact absurd (congrArg (Polynomial.eval 0) (toLaurent_injective (by simpa using h2 :
    toLaurent (Polynomial.C 2 : (ZMod 4)[X]) = toLaurent (Polynomial.C 2 * p * X))))
    (by simp only [eval_C, eval_mul, eval_X, mul_zero]; decide)

end Counterexample

end Grothendieck.Folder127
