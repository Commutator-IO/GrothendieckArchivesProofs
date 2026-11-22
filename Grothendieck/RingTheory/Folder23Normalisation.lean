module

public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Nagata.Basic
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.Nagata.Examples
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksFrontier.RingTheory.Nagata.Universes
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 23, pages 86 to 88: finiteness of the normalisation of a quotient of a regular ring

The *Remarque* of leaf 88 (finding `23-finite-normalisation-quotient-of-regular`): let `A` be a
domain that is a quotient of a regular ring. The integral closure of `A` in its field of
fractions is finite over `A` if and only if
* a) the primes `𝔭` of `A` with `A_𝔭` of dimension `1` and not regular are finite in number, and
* b) for each of them, the normalisation of `A_𝔭` is finite over `A_𝔭`.

Here « of dimension `1` » is `𝔭.height = 1` (`dim A_𝔭 = ht 𝔭`), « the normalisation is finite »
is Stacks' `IsN1` (tag 032F), and « regular » is Mathlib's `IsRegularLocalRing`. Conditions a)
and b) together are `NormalisationCriterion A`.

**What is proved.**
* `normalisationCriterion_of_isN1`: the necessity, for every Noetherian domain (the hypothesis
  « quotient of a regular ring » is not needed). The page calls it evident: the non-normal locus
  is closed. The proof here makes that concrete: if the integral closure `A'` is finite, a common
  denominator `d ≠ 0` of its generators satisfies `d A' ⊆ A`; every `A_𝔮` with `d ∉ 𝔮` is
  normal, hence regular when `ht 𝔮 = 1`; so the primes of a) are minimal over `(d)`, of which
  there are finitely many, and `A_𝔮'` lies in `d⁻¹ A_𝔮` for every `𝔮`, which gives b).
* `isRegularLocalRing_atPrime_of_isIntegrallyClosed`: in height one, normal implies regular
  (a one-dimensional Noetherian normal local domain is a discrete valuation ring).
* `isN1_iff_normalisationCriterion_of_isNagataRing`, `…_of_isExcellent`, `…_quotient`: the
  equivalence of the Remarque for a domain of finite type over a Nagata ring, in particular for
  a domain quotient `R ⧸ 𝔭` of an excellent ring `R` (Stacks 07QV: quasi-excellent rings are
  Nagata). This covers the quotients of the excellent regular rings: polynomial rings over a
  field, over `ℤ`, over a complete regular local ring (Stacks 07QW). In that case both sides hold
  (`isN1_of_finiteType_of_isNagataRing`, Stacks 0334), so the sufficiency is the finiteness of
  the normalisation of a Nagata domain, not the construction of leaves 87 and 86.
* `isN1_of_finiteType_field`, `isN1_quotient_of_isPrecomplete`: the two cases of a domain of
  finite type over a field and of a quotient of a complete Noetherian local ring.

**Not formalised.** The sufficiency for a quotient of an arbitrary regular ring, which need not
be excellent (nor of finite dimension). This is the content of leaves 87 and 86: an intermediate
`B`, finite over `A` and normal at the primes of a); the extension `C = i_* i^* B̃` across a
closed set of codimension `≥ 2`, coherent because `B̃` is `(S₂)` and the `(S₂)` locus of a
quotient of a regular ring is open; `C` is `(S₂)` and `(R₁)`, the latter because a quotient of a
regular ring is universally catenary, hence normal by Serre's criterion (Stacks 0345). The Stacks
declarations it would rest on (the `(S₂)` canonical module 0AWE, dualizing complexes, which need
finite dimension and so a localisation first) do not yet give the `S₂`-ification `Hom(ω, ω)` as
a finite extension, nor the coherence of `i_*` across codimension two. Nor is the lemma of leaf
86 on `(S_k)` along finite morphisms formalised.
-/

namespace Grothendieck.Folder23Normalisation

open IsLocalRing

/-- Conditions a) and b) of the Remarque on page 88: the height-one primes `𝔮` of `A` with
`A_𝔮` not regular form a finite set, and for each of them the normalisation of `A_𝔮` is finite
over `A_𝔮` (`IsN1`, Stacks 032F). -/
@[montpellier "23, 88"]
def NormalisationCriterion (A : Type*) [CommRing A] : Prop :=
  {q : PrimeSpectrum A | q.asIdeal.height = 1 ∧
      ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal)}.Finite ∧
    ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal) →
        IsN1 (Localization.AtPrime q.asIdeal)

/-- At a prime of height one of a Noetherian domain, a normal local ring is regular: it is a
one-dimensional Noetherian normal local domain, hence a principal ideal ring. -/
theorem isRegularLocalRing_atPrime_of_isIntegrallyClosed {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1)
    [IsIntegrallyClosed (Localization.AtPrime q)] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff,
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), hq]
    simp
  have h4 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ P : Ideal (Localization.AtPrime q),
      P ≠ ⊥ → P.IsPrime → P = maximalIdeal (Localization.AtPrime q) :=
    ⟨inferInstance, fun P hP hP' => eq_maximalIdeal (hP'.isMaximal_of_ne_bot hP)⟩
  have : IsPrincipalIdealRing (Localization.AtPrime q) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)).out 4 1).mp h4
  infer_instance

/-- If `d` multiplies the integral closure of `A` into `A`, then for every prime `𝔮` and every
`x` of `Frac A` integral over `A_𝔮`, the element `d x` comes from `A_𝔮`. -/
theorem exists_algebraMap_eq_smul_of_isIntegral {A : Type*} [CommRing A] [IsDomain A] {d : A}
    (hd : ∀ b ∈ Subalgebra.toSubmodule (integralClosure A (FractionRing A)),
      IsLocalization.IsInteger A (d • b))
    (q : Ideal A) [q.IsPrime] {x : FractionRing A}
    (hx : IsIntegral (Localization.AtPrime q) x) :
    ∃ z : Localization.AtPrime q,
      algebraMap (Localization.AtPrime q) (FractionRing A) z = d • x := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization q.primeCompl x hx
  have hm' : (m : A) • x ∈ Subalgebra.toSubmodule (integralClosure A (FractionRing A)) := by
    rw [Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
    exact hm
  obtain ⟨y, hy⟩ := RingHom.mem_rangeS.mp (hd _ hm')
  have hm0 : (m : A) ≠ 0 := fun h =>
    (Ideal.mem_primeCompl_iff.mp m.2) (by rw [h]; exact q.zero_mem)
  have hmK : algebraMap A (FractionRing A) (m : A) ≠ 0 := by
    have := (IsFractionRing.injective A (FractionRing A)).ne hm0
    rwa [map_zero] at this
  have h1 := congrArg (algebraMap (Localization.AtPrime q) (FractionRing A))
    (IsLocalization.mk'_spec (Localization.AtPrime q) y m)
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at h1
  refine ⟨IsLocalization.mk' (Localization.AtPrime q) y m, mul_right_cancel₀ hmK ?_⟩
  rw [h1, hy]
  simp only [Algebra.smul_def]
  ring

/-- **The necessity in the Remarque of page 88.** If the integral closure of a Noetherian
domain `A` is finite over `A` (`IsN1 A`), then the height-one primes `𝔮` with `A_𝔮` not regular
are finitely many, and the normalisation of each `A_𝔮` is finite. -/
@[montpellier "23, 88"]
theorem normalisationCriterion_of_isN1 (A : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (h : IsN1 A) : NormalisationCriterion A := by
  have hfg : (Subalgebra.toSubmodule (integralClosure A (FractionRing A))).FG :=
    Module.Finite.iff_fg.1 h
  obtain ⟨d, hdA, hd⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdA
  have hdK : algebraMap A (FractionRing A) d ≠ 0 := by
    have := (IsFractionRing.injective A (FractionRing A)).ne hd0
    rwa [map_zero] at this
  -- Away from `V(d)` the local rings are normal, hence regular in height one.
  have hreg : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 → d ∉ q.asIdeal →
      IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
    intro q hq hdq
    have : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) := by
      rw [isIntegrallyClosed_iff (FractionRing A)]
      intro x hx
      obtain ⟨z, hz⟩ := exists_algebraMap_eq_smul_of_isIntegral hd q.asIdeal hx
      obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime q.asIdeal)
        (⟨d, Ideal.mem_primeCompl_iff.mpr hdq⟩ : q.asIdeal.primeCompl)
      have hu' : (u : Localization.AtPrime q.asIdeal) =
          algebraMap A (Localization.AtPrime q.asIdeal) d := hu
      refine ⟨(↑u⁻¹ : Localization.AtPrime q.asIdeal) * z, ?_⟩
      rw [map_mul, hz, Algebra.smul_def,
        IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal) (FractionRing A) d,
        ← hu', ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    exact isRegularLocalRing_atPrime_of_isIntegrallyClosed q.asIdeal hq
  refine ⟨?_, fun q _ _ => ?_⟩
  · -- a): the primes in question are minimal over `(d)`.
    have hinj : Set.InjOn PrimeSpectrum.asIdeal
        (PrimeSpectrum.asIdeal ⁻¹' (Ideal.span {d}).minimalPrimes) :=
      fun _ _ _ _ hpq => PrimeSpectrum.ext hpq
    refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {d})).preimage
      hinj).subset ?_
    rintro q ⟨hq, hnreg⟩
    have hdq : d ∈ q.asIdeal := by
      by_contra hdq
      exact hnreg (hreg q hq hdq)
    have : q.asIdeal.FiniteHeight := ⟨Or.inr (by simp [hq])⟩
    show q.asIdeal ∈ (Ideal.span {d}).minimalPrimes
    refine Ideal.mem_minimalPrimes_of_height_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hdq) ?_
    rw [hq]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hdA
  · -- b): the normalisation of `A_𝔮` lies in `d⁻¹ A_𝔮`.
    refine MonogenicN1.isN1_of_module_finite _ (FractionRing A) ?_
    refine isN1_of_le_fg (Submodule.span (Localization.AtPrime q.asIdeal)
      {(algebraMap A (FractionRing A) d)⁻¹}) (Submodule.fg_span_singleton _) ?_
    intro x hx
    rw [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at hx
    obtain ⟨z, hz⟩ := exists_algebraMap_eq_smul_of_isIntegral hd q.asIdeal hx
    rw [Submodule.mem_span_singleton]
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, hz, Algebra.smul_def, mul_right_comm, mul_inv_cancel₀ hdK, one_mul]

/-- A domain of finite type over a Nagata ring has a finite normalisation (Stacks 0334 and
032R: it is Nagata, hence N-2, hence N-1). -/
theorem isN1_of_finiteType_of_isNagataRing {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A] (hR : IsNagataRing R) : IsN1 A := by
  have : IsJapaneseRing A :=
    MonogenicN1.isJapaneseRing_of_isNagataRing (IsNagataRing.of_finiteType (S := A) hR)
  exact IsJapaneseRing.finite (FractionRing A)

/-- **The Remarque of page 88 over a Nagata base.** For a domain `A` of finite type over a
Nagata ring, the normalisation of `A` is finite if and only if conditions a) and b) hold
(both sides are then true). -/
@[montpellier "23, 88"]
theorem isN1_iff_normalisationCriterion_of_isNagataRing {R A : Type*} [CommRing R] [CommRing A]
    [IsDomain A] [Algebra R A] [Algebra.FiniteType R A] (hR : IsNagataRing R) :
    IsN1 A ↔ NormalisationCriterion A := by
  have : IsNoetherianRing A := (IsNagataRing.of_finiteType (S := A) hR).isNoetherianRing
  exact ⟨normalisationCriterion_of_isN1 A, fun _ => isN1_of_finiteType_of_isNagataRing hR⟩

/-- **The Remarque of page 88 over an excellent base** (Stacks 07QV: a quasi-excellent ring is
Nagata). -/
@[montpellier "23, 88"]
theorem isN1_iff_normalisationCriterion_of_isExcellent {R A : Type*} [CommRing R] [CommRing A]
    [IsDomain A] [Algebra R A] [Algebra.FiniteType R A] (hR : IsExcellent R) :
    IsN1 A ↔ NormalisationCriterion A :=
  isN1_iff_normalisationCriterion_of_isNagataRing (isNagataRing_of_isQuasiExcellent hR.1)

/-- **The Remarque of page 88 for a domain quotient of an excellent ring**, e.g. of an excellent
regular ring: `R ⧸ 𝔭` has a finite normalisation if and only if conditions a) and b) hold. -/
@[montpellier "23, 88"]
theorem isN1_iff_normalisationCriterion_quotient {R : Type*} [CommRing R] (hR : IsExcellent R)
    (p : Ideal R) [p.IsPrime] : IsN1 (R ⧸ p) ↔ NormalisationCriterion (R ⧸ p) :=
  isN1_iff_normalisationCriterion_of_isExcellent (R := R) hR

/-- A domain of finite type over a field has a finite normalisation (Stacks 0335 (1)). -/
@[montpellier "23, 88"]
theorem isN1_of_finiteType_field (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] : IsN1 A :=
  isN1_of_finiteType_of_isNagataRing (IsNagataRing.of_field (K := k))

/-- A domain quotient of a complete Noetherian local ring has a finite normalisation (Stacks
032W). -/
@[montpellier "23, 88"]
theorem isN1_quotient_of_isPrecomplete (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsPrecomplete (maximalIdeal R) R] (p : Ideal R) [p.IsPrime] :
    IsN1 (R ⧸ p) :=
  isN1_of_finiteType_of_isNagataRing (R := R) IsNagataRing.of_isPrecomplete_maximalIdeal

end Grothendieck.Folder23Normalisation
