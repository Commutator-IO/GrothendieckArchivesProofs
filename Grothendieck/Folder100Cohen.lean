module

public import Grothendieck.Folder100
public import Grothendieck.Folder100Baire
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.NoetherNormalization.Basic

@[expose] public section

/-!
# Folder 100, page 38: the Corollary through Cohen's structure theorem

The modernised reading `transcripts/100/100.modern.tex` (« Un argument de Baire ») proves the
Corollary of page 38 (finding `100-baire-dimension-one-points` of `src/content/findings.ts`):
in `S = Spec R`, `R` a complete noetherian local domain, countably many nowhere-dense closed
subsets miss some point of dimension one. `Grothendieck/Folder100.lean` proves it, and the
Proposition of page 36, by countable prime avoidance, and the page's own route only for
`Θ = V⟦T⟧`; `Grothendieck/Folder100Baire.lean` does Baire on `𝔪ⁿ` for `Θ = V⟦T₁, …, Tₙ⟧`. This
file follows the page's route in every dimension, through Cohen's structure theorem.

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
* `good_mvPowerSeries_byVariables`: the same step by a second route, one variable at a time,
  without Baire.

**How.** The page's argument. By Cohen's structure theorem (Stacks 032D,
`IsLocalRing.exists_injective_finite_mvPowerSeries`, built on Stacks 0323 and 032A), `R` is
finite over a subring `A = Λ⟦T₁, …, T_d⟧`, `Λ` a field or a Cohen ring; when `Λ` is a field,
`A ≃ V⟦T₁, …, T_{d-1}⟧` with `V = Λ⟦T₀⟧` (`mvPowerSeriesEquiv`), as the reading's footnote says.
A proper closed `Zᵢ` lies in `V(gᵢ)`, `gᵢ ≠ 0`, and `gᵢ` has a nonzero multiple `aᵢ ∈ A`
(`R` is integral over `A`). The `V`-point of `Θ` is the evaluation at a point `a ∈ 𝔪ⁿ` where no
`aᵢ` vanishes, which Baire's theorem on the complete metric space `𝔪ⁿ` provides
(`good_mvPowerSeries`, from `Folder100Baire.exists_eval_ne_zero`: the zero set of a nonzero
series is closed with empty interior). The second route, `good_mvPowerSeries_byVariables`,
finds the point one variable at a time (`good_powerSeries`): for `a ∈ 𝔪_V`,
`B⟦T⟧ ⧸ (T − a) ≃ B` (`exists_evalHom`, `T − a` being distinguished), and a nonzero `f ∈ B⟦T⟧` lies in `(T − a)` for finitely many `a` only
(`finite_bad_of_separated`: a `V`-linear coefficient functional `B → V` sends `f` to a nonzero
`g ∈ V⟦T⟧` with `g ∈ (T − a)`, and `Folder100.finite_bad` applies to `g`); as `𝔪_V` is
uncountable (`Folder100.uncountable`), some `a` avoids all the `fᵢ` (`exists_avoid_separated`).
This choice, variable after variable, avoids Baire. Finally
a prime `Q` of `R` over the point `P` of `A` (lying over) is outside every `Zᵢ`, since
`aᵢ ∉ P`, and `dim R ⧸ Q = dim A ⧸ P = 1`, `R ⧸ Q` being integral over `A ⧸ P`
(`ringKrullDim_eq_of_injective_isIntegral`, Stacks).

**Not formalised.** The Proposition of page 36 is not deduced from the
Corollary here (it is proved in `Folder100.lean` by another route), nor is the application to
the algebraisation of formal abelian schemes.
-/

namespace Grothendieck.Folder100Cohen

open IsLocalRing
open scoped Polynomial PowerSeries

universe u

/-! ### The bad constants of one series -/

section Constants

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V]

/-- `ι : V → B` such that the nonzero elements of `B` are seen by `V`-linear functionals. -/
def Separated {B : Type*} [CommRing B] (ι : V →+* B) : Prop :=
  ∀ b : B, b ≠ 0 → ∃ l : B →+ V, (∀ v x, l (ι v * x) = v * l x) ∧ l b ≠ 0

/-- The constants `c ∈ 𝔪_V` such that `f ∈ (T − c)`. -/
def bad {B : Type*} [CommRing B] (ι : V →+* B) (f : B⟦X⟧) : Set V :=
  {c | c ∈ maximalIdeal V ∧ f ∈ Ideal.span {PowerSeries.X - PowerSeries.C (ι c)}}

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] in
/-- A `V`-linear functional `l : B → V`, applied coefficientwise, maps `(T − c)` into `(T − c)`. -/
lemma mk_mem_span {B : Type*} [CommRing B] (ι : V →+* B) (l : B →+ V)
    (hl : ∀ v x, l (ι v * x) = v * l x) {c : V} {f : B⟦X⟧}
    (hf : f ∈ Ideal.span {PowerSeries.X - PowerSeries.C (ι c)}) :
    PowerSeries.mk (fun n => l (PowerSeries.coeff n f)) ∈
      Ideal.span {PowerSeries.X - PowerSeries.C c} := by
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  have hl' : ∀ x, l (x * ι c) = l x * c := fun x => by rw [mul_comm x, hl, mul_comm]
  refine Ideal.mem_span_singleton'.2 ⟨PowerSeries.mk fun n => l (PowerSeries.coeff n h), ?_⟩
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n <;>
    simp [PowerSeries.coeff_mk, mul_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_succ_mul_X, hl']

/-- A nonzero `f ∈ B⟦T⟧` lies in `(T − c)` for finitely many `c ∈ 𝔪_V` only. -/
theorem finite_bad_of_separated {B : Type*} [CommRing B] (ι : V →+* B) (hsep : Separated ι)
    {f : B⟦X⟧} (hf : f ≠ 0) : (bad ι f).Finite := by
  obtain ⟨n, hn⟩ : ∃ n, PowerSeries.coeff n f ≠ 0 := by
    by_contra! h
    exact hf (PowerSeries.ext fun n => by simpa using h n)
  obtain ⟨l, hl, hln⟩ := hsep _ hn
  have hg : PowerSeries.mk (fun n => l (PowerSeries.coeff n f)) ≠ 0 := fun h0 =>
    hln (by simpa using congrArg (PowerSeries.coeff n) h0)
  exact (Grothendieck.Folder100.finite_bad hg).subset fun c ⟨hc, hm⟩ =>
    ⟨hc, mk_mem_span ι l hl hm⟩

/-- Countably many nonzero `fᵢ ∈ B⟦T⟧` leave a constant `c ∈ 𝔪_V` with every `fᵢ ∉ (T − c)`. -/
theorem exists_avoid_separated {B : Type*} [CommRing B] (ι : V →+* B) (hsep : Separated ι)
    (S : Set B⟦X⟧) (hS : S.Countable) (h0 : (0 : B⟦X⟧) ∉ S) :
    ∃ c ∈ maximalIdeal V, ∀ f ∈ S, f ∉ Ideal.span {PowerSeries.X - PowerSeries.C (ι c)} := by
  by_contra! h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hc : (⋃ f ∈ S, bad ι f).Countable :=
    hS.biUnion fun f hf => (finite_bad_of_separated ι hsep fun h' => h0 (h' ▸ hf)).countable
  have hϖm : ϖ ∈ maximalIdeal V := hϖ.not_isUnit
  have : Countable V := by
    have := hc.to_subtype
    refine Function.Injective.countable (f := fun x : V => (⟨ϖ * x, ?_⟩ : ↥(⋃ f ∈ S, bad ι f))) ?_
    · obtain ⟨f, hf, hm⟩ := h (ϖ * x) (Ideal.mul_mem_right x _ hϖm)
      exact Set.mem_biUnion hf (show ϖ * x ∈ bad ι f from ⟨Ideal.mul_mem_right x _ hϖm, hm⟩)
    · intro x y hxy
      exact mul_left_cancel₀ hϖ.ne_zero (congrArg Subtype.val hxy)
  have hu : Uncountable V := Grothendieck.Folder100.uncountable (V := V)
  exact not_countable this

end Constants

/-! ### `B⟦T⟧ ⧸ (T − b) ≃ B` -/

section Eval

variable {B : Type*} [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B]

omit [IsAdicComplete (maximalIdeal B) B] in
/-- `T − b`, for `b ∈ 𝔪_B`, is distinguished. -/
lemma isDistinguishedAt_X_sub_C {b : B} (hb : b ∈ maximalIdeal B) :
    (Polynomial.X - Polynomial.C b).IsDistinguishedAt (maximalIdeal B) where
  mem {n} hn := by
    rw [Polynomial.natDegree_X_sub_C, Nat.lt_one_iff] at hn
    subst hn
    simpa using hb
  monic := Polynomial.monic_X_sub_C b

/-- For `b ∈ 𝔪_B`, a surjection `B⟦T⟧ → B` with kernel `(T − b)`. -/
theorem exists_evalHom {b : B} (hb : b ∈ maximalIdeal B) :
    ∃ ψ : B⟦X⟧ →+* B, Function.Surjective ψ ∧
      ∀ f, ψ f = 0 ↔ f ∈ Ideal.span {PowerSeries.X - PowerSeries.C b} := by
  let e : (B⟦X⟧ ⧸ Ideal.span {PowerSeries.X - PowerSeries.C b}) ≃ₐ[B] B :=
    (Ideal.quotientEquivAlgOfEq B (by rw [Grothendieck.Folder100.coe_X_sub_C])).trans
      ((isDistinguishedAt_X_sub_C hb).algEquivQuotient.symm.trans
        (Polynomial.quotientSpanXSubCAlgEquiv b))
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk _), fun y => ?_, fun f => ?_⟩
  · obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨f, rfl⟩
  · change e (Ideal.Quotient.mk _ f) = 0 ↔ _
    rw [map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]

end Eval

/-! ### `V`-points avoiding countably many series -/

section Good

/-- Countably many nonzero elements of `B` stay nonzero under some surjection `B → V`. -/
def Good (V B : Type*) [CommRing V] [CommRing B] : Prop :=
  ∀ S : Set B, S.Countable → (0 : B) ∉ S → ∃ φ : B →+* V, Function.Surjective φ ∧ ∀ s ∈ S, φ s ≠ 0

variable {V : Type*} [CommRing V]

lemma good_self : Good V V := fun _ _ h0 =>
  ⟨RingHom.id V, Function.surjective_id, fun s hs h =>
    h0 (by rw [RingHom.id_apply] at h; rwa [h] at hs)⟩

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

/-- The step of the page, one variable at a time. -/
theorem good_powerSeries [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] {B : Type*} [CommRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] (ι : V →+* B)
    (hι : ∀ c ∈ maximalIdeal V, ι c ∈ maximalIdeal B) (hsep : Separated ι) (h : Good V B) :
    Good V B⟦X⟧ := by
  intro S hS h0
  obtain ⟨c, hc, hcS⟩ := exists_avoid_separated ι hsep S hS h0
  obtain ⟨ψ, hψ, hψ0⟩ := exists_evalHom (hι c hc)
  obtain ⟨φ, hφ, hφS⟩ := h (ψ '' S) (hS.image ψ) (by
    rintro ⟨s, hs, hs0⟩
    exact hcS s hs ((hψ0 s).1 hs0))
  refine ⟨φ.comp ψ, by rw [RingHom.coe_comp]; exact hφ.comp hψ, fun s hs => hφS _ ⟨s, hs, rfl⟩⟩

/-- The kernel of the surjection is a point with `B ⧸ P ≃ V`, of dimension one. -/
theorem Good.exists_prime [IsDomain V] [IsDiscreteValuationRing V] {B : Type*} [CommRing B]
    (h : Good V B) (S : Set B) (hS : S.Countable) (h0 : (0 : B) ∉ S) :
    ∃ P : Ideal B, P.IsPrime ∧ ringKrullDim (B ⧸ P) = 1 ∧ ∀ s ∈ S, s ∉ P := by
  obtain ⟨φ, hφ, hφS⟩ := h S hS h0
  refine ⟨RingHom.ker φ, RingHom.ker_isPrime φ, ?_, fun s hs hk => hφS s hs (RingHom.mem_ker.1 hk)⟩
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ)]
  exact IsDiscreteValuationRing.ringKrullDim_eq_one V

variable [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] in
lemma separated_C (n : ℕ) : Separated (MvPowerSeries.C : V →+* MvPowerSeries (Fin n) V) := by
  intro b hb
  obtain ⟨α, hα⟩ : ∃ α, MvPowerSeries.coeff α b ≠ 0 := by
    by_contra! h
    exact hb (MvPowerSeries.ext fun α => by simpa using h α)
  exact ⟨(MvPowerSeries.coeff α).toAddMonoidHom, fun v x => by simp [MvPowerSeries.coeff_C_mul],
    by simpa using hα⟩

omit [IsAdicComplete (maximalIdeal V) V] in
lemma C_mem_maximalIdeal (n : ℕ) {c : V} (hc : c ∈ maximalIdeal V) :
    (MvPowerSeries.C c : MvPowerSeries (Fin n) V) ∈ maximalIdeal (MvPowerSeries (Fin n) V) :=
  (mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => mem_nonunits_iff.1
    ((mem_maximalIdeal _).1 hc) (by simpa using hu.map (MvPowerSeries.constantCoeff)))

/-- The step on `Θ = V⟦T₁, …, Tₙ⟧` by a second route: countably many nonzero series stay nonzero
under some surjection `Θ → V`, chosen one variable at a time (no Baire). -/
theorem good_mvPowerSeries_byVariables : ∀ n : ℕ, Good V (MvPowerSeries (Fin n) V)
  | 0 => Good.of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) V).toRingEquiv.symm good_self
  | n + 1 => by
    have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) V)) (MvPowerSeries (Fin n) V) :=
      Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_mvPowerSeries V n
    exact Good.of_ringEquiv (MvPowerSeries.finSuccEquiv V n).toRingEquiv.symm
      (good_powerSeries MvPowerSeries.C (fun _ hc => C_mem_maximalIdeal n hc) (separated_C n)
        (good_mvPowerSeries_byVariables n))

/-- **The page's step on `Θ = V⟦T₁, …, Tₙ⟧`, by Baire on `𝔪ⁿ`**: countably many nonzero series
stay nonzero under the evaluation `Θ → V` at some `a ∈ 𝔪ⁿ`
(`Folder100Baire.exists_eval_ne_zero`). -/
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
