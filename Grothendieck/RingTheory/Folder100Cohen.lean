module

public import Grothendieck.RingTheory.Folder100
public import Grothendieck.RingTheory.Folder100Baire
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.NoetherNormalization.Basic
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 100, page 38: the Corollary through Cohen's structure theorem

The modernised reading `transcripts/100/100.modern.tex` (« Un argument de Baire ») proves the
Corollary of page 38 (finding `100-baire-dimension-one-points` of `src/content/findings.ts`):
in `S = Spec R`, `R` a complete noetherian local domain, countably many nowhere-dense closed
subsets miss some point of dimension one. `Grothendieck/RingTheory/Folder100.lean` proves it, and
the Proposition of page 36, by countable prime avoidance, and the page's own route only for
`Θ = V⟦T⟧`; `Grothendieck/RingTheory/Folder100Baire.lean` does Baire on `𝔪ⁿ` for `Θ = V⟦T₁, …, Tₙ⟧`.
This file follows the page's route in every dimension, through Cohen's structure theorem.

**What is proved.**
* `exists_coheight_eq_one_of_cohen`: the Corollary of page 38. Let `R` be a complete noetherian
  local domain which is not a field, and `(Zᵢ)` a countable family of proper closed subsets of
  `Spec R` (the « fermés rares » of the irreducible `Spec R`). Some point `x` of coheight `1`
  (`dim closure {x} = 1`, see `Folder100.Baire.topologicalKrullDim_closure_singleton`) lies in no
  `Zᵢ`.
* `Good.exists_prime`, `good_mvPowerSeries`: the step on `Θ = V⟦T₁, …, Tₙ⟧`, `V` a complete
  discrete valuation ring: countably many nonzero `fᵢ ∈ Θ` lie outside the kernel `P` of some
  surjection `Θ → V`, a point of `Spec Θ` with `Θ ⧸ P ≃ V`, of dimension one. The surjection
  is the `V`-linear evaluation at a point of `𝔪ⁿ` given by Baire
  (`Folder100Baire.exists_eval_ne_zero`).

**How.** The page's argument. By Cohen's structure theorem (Stacks 032D,
`IsLocalRing.exists_injective_finite_mvPowerSeries`, built on Stacks 0323 and 032A), `R` is
finite over a subring `A = Λ⟦T₁, …, T_d⟧`, `Λ` a field or a Cohen ring; when `Λ` is a field,
`A ≃ V⟦T₁, …, T_{d-1}⟧` with `V = Λ⟦T₀⟧` (`mvPowerSeriesEquiv`), as the reading's footnote says.
A proper closed `Zᵢ` lies in `V(gᵢ)`, `gᵢ ≠ 0`, and `gᵢ` has a nonzero multiple `aᵢ ∈ A`
(`R` is integral over `A`). The `V`-point of `Θ` is the evaluation at a point `a ∈ 𝔪ⁿ` where no
`aᵢ` vanishes, which Baire's theorem on the complete metric space `𝔪ⁿ` provides
(`good_mvPowerSeries`, from `Folder100Baire.exists_eval_ne_zero`: the zero set of a nonzero
series is closed with empty interior). Finally a prime `Q` of `R` over the point `P` of `A`
(lying over) is outside every `Zᵢ`, since `aᵢ ∉ P`, and `dim R ⧸ Q = dim A ⧸ P = 1`, `R ⧸ Q` being integral over `A ⧸ P`
(`ringKrullDim_eq_of_injective_isIntegral`, Stacks).

**Not formalised.** The Proposition of page 36 is not deduced from the Corollary here (it is
proved in `Folder100.lean` by another route), nor is the application to the algebraisation of
formal abelian schemes.
-/

namespace Grothendieck.Folder100Cohen

open IsLocalRing
open scoped PowerSeries

universe u

/-! ### `V`-points avoiding countably many series -/

section Good

/-- Countably many nonzero elements of `B` stay nonzero under some surjection `B → V`. -/
def Good (V B : Type*) [CommRing V] [CommRing B] : Prop :=
  ∀ S : Set B, S.Countable → (0 : B) ∉ S → ∃ φ : B →+* V, Function.Surjective φ ∧ ∀ s ∈ S, φ s ≠ 0

variable {V : Type*} [CommRing V]

lemma Good.of_ringEquiv {B B' : Type*} [CommRing B] [CommRing B'] (e : B ≃+* B')
    (h : Good V B) : Good V B' := by
  intro S hS h0
  obtain ⟨φ, hφ, hS'⟩ := h (e.symm '' S) (hS.image _) (by
    rintro ⟨s, hs, hs0⟩
    rw [map_eq_zero_iff _ e.symm.injective] at hs0
    exact h0 (hs0 ▸ hs))
  refine ⟨φ.comp e.symm.toRingHom, fun y => ?_, fun s hs => hS' _ ⟨s, hs, rfl⟩⟩
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨e x, by simp⟩

/-- The kernel of the surjection is a point with `B ⧸ P ≃ V`, of dimension one. -/
@[montpellier "100, 38"]
theorem Good.exists_prime [IsDomain V] [IsDiscreteValuationRing V] {B : Type*} [CommRing B]
    (h : Good V B) (S : Set B) (hS : S.Countable) (h0 : (0 : B) ∉ S) :
    ∃ P : Ideal B, P.IsPrime ∧ ringKrullDim (B ⧸ P) = 1 ∧ ∀ s ∈ S, s ∉ P := by
  obtain ⟨φ, hφ, hφS⟩ := h S hS h0
  refine ⟨RingHom.ker φ, RingHom.ker_isPrime φ, ?_, fun s hs hk => hφS s hs (RingHom.mem_ker.1 hk)⟩
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ)]
  exact IsDiscreteValuationRing.ringKrullDim_eq_one V

variable [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]

/-- **The page's step on `Θ = V⟦T₁, …, Tₙ⟧`, by Baire on `𝔪ⁿ`**: countably many nonzero series
stay nonzero under the evaluation `Θ → V` at some `a ∈ 𝔪ⁿ`
(`Folder100Baire.exists_eval_ne_zero`). -/
@[montpellier "100, 38"]
theorem good_mvPowerSeries (n : ℕ) : Good V (MvPowerSeries (Fin n) V) := by
  intro S hS h0
  have := hS.to_subtype
  obtain ⟨a, ha, h⟩ := Folder100Baire.exists_eval_ne_zero
    (fun s : S => (s : MvPowerSeries (Fin n) V)) fun s hs => h0 (hs ▸ s.2)
  exact ⟨(Folder100Baire.eval ha).toRingHom, Folder100Baire.eval_surjective ha,
    fun s hs => h ⟨s, hs⟩⟩

end Good

/-! ### The Corollary of page 38 -/

section Corollary

/-- `PowerSeries.map` of a ring isomorphism. -/
noncomputable def powerSeriesMapEquiv {A A' : Type*} [CommRing A] [CommRing A'] (e : A ≃+* A') :
    A⟦X⟧ ≃+* A'⟦X⟧ :=
  RingEquiv.ofRingHom (PowerSeries.map e.toRingHom) (PowerSeries.map e.symm.toRingHom)
    (RingHom.ext fun f => PowerSeries.ext fun n => by simp [PowerSeries.coeff_map])
    (RingHom.ext fun f => PowerSeries.ext fun n => by simp [PowerSeries.coeff_map])

/-- `finSuccEquiv` as a ring isomorphism. -/
noncomputable def finSuccRingEquiv (A : Type*) [CommRing A] (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) A ≃+* (MvPowerSeries (Fin n) A)⟦X⟧ :=
  (MvPowerSeries.finSuccEquiv A n).toRingEquiv

/-- `isEmptyEquiv` as a ring isomorphism. -/
noncomputable def isEmptyRingEquiv (A : Type*) [CommRing A] : MvPowerSeries (Fin 0) A ≃+* A :=
  (MvPowerSeries.isEmptyEquiv (Fin 0) A).toRingEquiv

/-- `Λ⟦T₀, …, Tₘ⟧ ≃ V⟦T₁, …, Tₘ⟧` with `V = Λ⟦T₀⟧`. -/
noncomputable def mvPowerSeriesEquiv (Λ : Type*) [CommRing Λ] :
    (m : ℕ) → MvPowerSeries (Fin (m + 1)) Λ ≃+* MvPowerSeries (Fin m) Λ⟦X⟧
  | 0 => (finSuccRingEquiv Λ 0).trans
      ((powerSeriesMapEquiv (isEmptyRingEquiv Λ)).trans
        (isEmptyRingEquiv Λ⟦X⟧).symm)
  | m + 1 => (finSuccRingEquiv Λ (m + 1)).trans
      ((powerSeriesMapEquiv (mvPowerSeriesEquiv Λ m)).trans
        (finSuccRingEquiv Λ⟦X⟧ m).symm)

/-- The point of dimension one on the regular subring `Λ⟦T₁, …, T_d⟧` given by Cohen's theorem. -/
theorem exists_prime_of_cohen (Λ : Type*) [CommRing Λ] [IsDomain Λ]
    (hΛ : IsField Λ ∨ IsCohenRing Λ) (d : ℕ) (hd : IsField Λ → d ≠ 0)
    (S : Set (MvPowerSeries (Fin d) Λ)) (hS : S.Countable) (h0 : 0 ∉ S) :
    ∃ P : Ideal (MvPowerSeries (Fin d) Λ), P.IsPrime ∧
      ringKrullDim (MvPowerSeries (Fin d) Λ ⧸ P) = 1 ∧ ∀ s ∈ S, s ∉ P := by
  rcases hΛ with hΛ | hΛ
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hd hΛ)
    let := hΛ.toField
    have : IsAdicComplete (maximalIdeal Λ) Λ := by
      rw [maximalIdeal_eq_bot]
      infer_instance
    have : IsAdicComplete (maximalIdeal Λ⟦X⟧) Λ⟦X⟧ :=
      Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_powerSeries Λ
    exact (Good.of_ringEquiv (mvPowerSeriesEquiv Λ m).symm
      (good_mvPowerSeries (V := Λ⟦X⟧) m)).exists_prime S hS h0
  · exact (good_mvPowerSeries (V := Λ) d).exists_prime S hS h0

/-- **Corollary of page 38, by the page's route.** Let `R` be a complete noetherian local domain
which is not a field. Countably many proper closed subsets of `Spec R` miss some point `x` of
coheight one (`dim closure {x} = 1`). Through Cohen's structure theorem, `R` is finite over
`A = Λ⟦T₁, …, T_d⟧`; a point of dimension one of `A` avoiding nonzero elements `aᵢ` of `A`
under the `Zᵢ` is found variable by variable, and lifted to `R`. -/
@[montpellier "100, 38"]
theorem exists_coheight_eq_one_of_cohen (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R] (hR : ¬ IsField R)
    {ι : Type*} [Countable ι] (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hZu : ∀ i, Z i ≠ Set.univ) :
    ∃ x : PrimeSpectrum R, Order.coheight x = 1 ∧ ∀ i, x ∉ Z i := by
  obtain ⟨d, Λ, _, _, hΛ, _, _, f, hfinj, hfin, -⟩ :=
    IsLocalRing.exists_injective_finite_mvPowerSeries R
  let := f.toAlgebra
  have : Algebra.IsIntegral (MvPowerSeries (Fin d) Λ) R := ⟨hfin.to_isIntegral⟩
  have hd : IsField Λ → d ≠ 0 := by
    rintro hΛf rfl
    exact hR (isField_of_isIntegral_of_isField' (R := MvPowerSeries (Fin 0) Λ)
      (MulEquiv.isField hΛf (MvPowerSeries.isEmptyEquiv (Fin 0) Λ).toRingEquiv.toMulEquiv))
  have hI : ∀ i, PrimeSpectrum.vanishingIdeal (Z i) ≠ ⊥ := by
    intro i h
    apply hZu i
    rw [← (hZ i).closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, h,
      PrimeSpectrum.zeroLocus_bot]
  have hJ : ∀ i, (PrimeSpectrum.vanishingIdeal (Z i)).under (MvPowerSeries (Fin d) Λ) ≠ ⊥ :=
    fun i h => hI i (Ideal.eq_bot_of_under_eq_bot h)
  choose a ha ha0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hJ i)
  obtain ⟨P, hP, hPdim, hPS⟩ := exists_prime_of_cohen Λ hΛ d hd (Set.range a)
    (Set.countable_range a) (by rintro ⟨i, hi⟩; exact ha0 i hi)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := R) P (fun x hx => by
    rw [RingHom.mem_ker] at hx
    rw [hfinj (hx.trans (map_zero f).symm)]
    exact P.zero_mem)
  subst hQP
  let x : PrimeSpectrum R := ⟨Q, hQ⟩
  refine ⟨x, ?_, fun i hx => hPS (a i) ⟨i, rfl⟩ (Ideal.mem_comap.2
    ((PrimeSpectrum.mem_vanishingIdeal _ _).1 (Ideal.mem_comap.1 (ha i)) x hx))⟩
  have hc : ringKrullDim (R ⧸ x.asIdeal) = Order.coheight x := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    rfl
  have hdim : ringKrullDim (R ⧸ Q) = 1 := by
    rw [← hPdim]
    exact (ringKrullDim_eq_of_injective_isIntegral
      (Ideal.quotientMap Q (algebraMap (MvPowerSeries (Fin d) Λ) R) le_rfl)
      Ideal.quotientMap_injective (RingHom.IsIntegral.quotient _ hfin.to_isIntegral)).symm
  have h1 : (Order.coheight x : WithBot ℕ∞) = 1 := hc.symm.trans hdim
  exact WithBot.coe_inj.1 (by rw [h1]; rfl)

end Corollary

end Grothendieck.Folder100Cohen
