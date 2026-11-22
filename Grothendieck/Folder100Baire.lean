module

public import Grothendieck.Folder100

@[expose] public section

/-!
# Folder 100, pages 36–38: Baire's theorem on `𝔪ⁿ`

The modernised reading `transcripts/100/100.modern.tex` (« Un argument de Baire ») proves the
Corollary of page 38 (finding `100-baire-dimension-one-points` of `src/content/findings.ts`) by
reducing to `Θ = V⟦T₁, …, Tₙ⟧`, `V` a complete discrete valuation ring: the `V`-homomorphisms
`Θ → V` are parametrised by `𝔪ⁿ`, the zeros of a nonzero `f ∈ Θ` form a closed subset with
empty interior of the complete metric space `𝔪ⁿ`, and Baire gives a point `a ∈ 𝔪ⁿ` where
countably many nonzero `fᵢ` do not vanish. `Grothendieck/Folder100.lean` proves the case
`n = 1` by countability, and `Grothendieck/Folder100Cohen.lean` chooses the point one variable
at a time; this file follows the page's own route in every `n`.

**What is proved.**
* `eval`: for `a ∈ 𝔪ⁿ`, the evaluation `Θ → V`, `T ↦ a` (Mathlib's `MvPowerSeries.aeval`, `V`
  carrying its `𝔪`-adic topology, complete and Hausdorff).
* `ker_eval`, `quotEquiv`: its kernel is `(T₁ − a₁, …, Tₙ − aₙ)` and `Θ ⧸ (T − a) ≃ V`.
* `eq_eval`, `exists_eq_eval`, `eval_injective`: **the parametrisation**. A `V`-algebra
  homomorphism `φ : Θ → V` with `φ(Tᵢ) ∈ 𝔪` (for instance a local one) is the evaluation at
  `(φ(T₁), …, φ(Tₙ))`; distinct points give distinct evaluations.
* `eval_sub_eval_mem`: `b ≡ a (mod 𝔪ᴺ)` implies `f(b) ≡ f(a) (mod 𝔪ᴺ)`.
* `eq_zero_of_eval_eq_zero`: a series vanishing on a product of infinite subsets of `𝔪` is `0`.
* `isClosed_zeroSet`, `interior_zeroSet`: for `f ≠ 0` the zero set `{a ∈ 𝔪ⁿ | f(a) = 0}` is
  closed with empty interior in `Vⁿ`.
* `exists_eval_ne_zero`: **Baire.** Countably many nonzero `fᵢ` have a common non-zero point
  `a ∈ 𝔪ⁿ`.
* `exists_avoid`: the several-variable `Folder100.exists_avoid`. The kernel `𝔭 = (T − a)` of the
  evaluation at that point is a prime with `Θ ⧸ 𝔭 ≃ V`, of coheight one in `Spec Θ`
  (`coheight_ker`; `dim closure {x} = 1`, see
  `Folder100.Baire.topologicalKrullDim_closure_singleton`), containing no `fᵢ`.
* `exists_avoid_of_isIntegral`, `exists_coheight_eq_one_of_isIntegral`: the lifting along a
  finite extension, and the Corollary of page 38 for a domain `R` integral over `Θ` (`Θ → R`
  injective): countably many nonzero `gᵢ ∈ R`, or proper closed subsets of `Spec R`, are
  avoided by a point of coheight one.

**How.** The evaluation is `MvPowerSeries.aeval`. Its kernel is `(T − a)` by Krull's
intersection theorem in the noetherian local ring `Θ` (`Folder100.Baire.exists_notMem_sup_pow`):
writing `f = p + r`, `p` the truncation of `f` in total degree `< N` and `r ∈ (T₁, …, Tₙ)ᴺ`
(`sub_truncTotal_mem`, from `eq_sum_X_mul_quot`: a series without constant term is `∑ Tᵢ gᵢ`),
one has `f − f(a) ∈ (T − a) + 𝔪_Θᴺ` for every `N`, the polynomial `p` being `p(a)` modulo
`(T − a)`. The parametrisation follows: `φ` kills `T − a`, hence `f − f(a)`. The congruence
`f(b) ≡ f(a)` gives the closedness of the zero sets. The identity principle is proved by
induction on `n` through `V⟦T₀, …, Tₙ⟧ ≃ V⟦T₁, …, Tₙ⟧⟦T₀⟧` (`MvPowerSeries.finSuccEquiv`):
evaluating at `(c, b)` is evaluating at `c` the series `f(T₀, b) ∈ V⟦T₀⟧` (`eval_cons`, by the
parametrisation), which has finitely many zeros in `𝔪` unless it is `0`
(`Folder100.finite_bad`); since a neighbourhood `a + (𝔪ᴹ)ⁿ` is a product of infinite sets
(`Folder100.uncountable`), a series vanishing on an open subset of `𝔪ⁿ` is `0`. Finally `Vⁿ`
is complete with a countably generated uniformity, hence completely metrisable and a Baire
space (Mathlib's `BaireSpace.of_completelyPseudoMetrizable`), and `𝔪ⁿ` is a nonempty open
subset. A prime strictly above `(T − a)` is maximal (`V` is a principal ideal domain), so
`(T − a)` has coheight one. Along an integral extension `Θ ⊂ R`, each `gᵢ ≠ 0` has a nonzero
multiple in `Θ` (`Ideal.under_ne_bot_of_integral_mem`), a prime `Q` lies over `(T − a)`, and
going-up, incomparability and the maximality criteria for integral extensions (Mathlib) give
coheight one for `Q`.

**Not formalised.** Cohen's structure theorem itself (Stacks 032D) is not invoked here, to keep
this file on Mathlib only: a complete noetherian local domain is finite over `Λ⟦T₁, …, T_d⟧`,
`Λ` a field or a Cohen ring, and when `Λ` is a field one still has to rewrite
`Λ⟦T₁, …, T_d⟧ ≃ V⟦T₂, …, T_d⟧` with `V = Λ⟦T₁⟧`; both steps are done in
`Grothendieck/Folder100Cohen.lean` (`exists_coheight_eq_one_of_cohen`), where the present
`exists_avoid` could replace `good_mvPowerSeries`. `𝔪ⁿ` is treated as an open subset of `Vⁿ`
with the product of the `𝔪`-adic topologies, not given an explicit metric. The Proposition of
page 36 is not deduced from the Corollary by this route (it is proved in `Folder100.lean` by
countable prime avoidance), nor is the application to formal abelian schemes.
-/

namespace Grothendieck.Folder100Baire

open IsLocalRing Topology Filter MvPowerSeries.WithPiTopology
open scoped PowerSeries

variable {V : Type*} [CommRing V] {n : ℕ}

/-- The `𝔪`-adic topology on `V`. -/
@[reducible] def withIdeal (V : Type*) [CommRing V] [IsLocalRing V] : WithIdeal V :=
  ⟨maximalIdeal V⟩

attribute [local instance] withIdeal

lemma isAdic [IsLocalRing V] : IsAdic (maximalIdeal V) := rfl

lemma isOpen_pow [IsLocalRing V] (N : ℕ) : IsOpen ((maximalIdeal V ^ N : Ideal V) : Set V) :=
  (isAdic_iff.1 isAdic).1 N

local instance [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] : CompleteSpace V :=
  ((isAdic.isAdicComplete_iff).1 inferInstance).1

local instance [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] : T2Space V :=
  ((isAdic.isAdicComplete_iff).1 inferInstance).2

section Vars

variable {R : Type*} [CommRing R]

open MvPowerSeries

/-- The ideal `(T₁, …, Tₙ)` of `R⟦T₁, …, Tₙ⟧`. -/
noncomputable def vars (R : Type*) [CommRing R] (n : ℕ) : Ideal (MvPowerSeries (Fin n) R) :=
  Ideal.span (Set.range X)

/-- The coefficients of `f` divided by `Tᵢ`, at the monomials whose first variable is `Tᵢ`. -/
noncomputable def quot (f : MvPowerSeries (Fin n) R) (i : Fin n) : MvPowerSeries (Fin n) R :=
  fun e => if ∀ j < i, e j = 0 then coeff (e + Finsupp.single i 1) f else 0

lemma coeff_quot (f : MvPowerSeries (Fin n) R) (i : Fin n) (e : Fin n →₀ ℕ) :
    coeff e (quot f i) = if ∀ j < i, e j = 0 then coeff (e + Finsupp.single i 1) f else 0 :=
  rfl

/-- A series without constant term is `∑ Tᵢ gᵢ`. -/
lemma eq_sum_X_mul_quot {f : MvPowerSeries (Fin n) R} (hf : constantCoeff f = 0) :
    f = ∑ i, X i * quot f i := by
  ext d
  simp only [map_sum, X, coeff_monomial_mul, one_mul, coeff_quot]
  by_cases hd : d = 0
  · subst hd
    rw [Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun h => absurd
      (Finsupp.single_le_iff.1 h) (by simp)]
    simpa using hf
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∈ d.support ∧ ∀ j ∈ d.support, i₀ ≤ j :=
    ⟨d.support.min' (Finsupp.support_nonempty_iff.2 hd), Finset.min'_mem _ _,
      fun j hj => Finset.min'_le _ _ hj⟩
  have hlow : ∀ j < i₀, d j = 0 := fun j hj => by
    by_contra h
    exact absurd (hi₀.2 j (Finsupp.mem_support_iff.2 h)) (not_le.2 hj)
  rw [Finset.sum_eq_single i₀]
  · have hle : Finsupp.single i₀ 1 ≤ d :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi₀.1))
    have hlow' : ∀ j < i₀, (d - Finsupp.single i₀ (1 : ℕ)) j = 0 := fun j hj => by
      simp [hj.ne, hlow j hj]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hle), ite_eq_left_of_eq_true _ _ (eq_true hlow'),
      tsub_add_cancel_of_le hle]
  · intro i _ hi
    split_ifs with h1 h2
    · exfalso
      have hdi : d i ≠ 0 := by
        have := Finsupp.single_le_iff.1 h1
        omega
      rcases lt_or_gt_of_ne hi with hlt | hlt
      · exact hdi (hlow i hlt)
      · have := h2 i₀ hlt
        simp only [Finsupp.tsub_apply, Finsupp.single_apply, hi, ↓reduceIte,
          tsub_zero] at this
        exact Finsupp.mem_support_iff.1 hi₀.1 this
    · rfl
    · rfl
  · simp

/-- A series whose coefficients vanish in degrees `< N` lies in `(T₁, …, Tₙ)ᴺ`. -/
lemma mem_vars_pow : ∀ (N : ℕ) {f : MvPowerSeries (Fin n) R},
    (∀ d : Fin n →₀ ℕ, d.degree < N → coeff d f = 0) → f ∈ vars R n ^ N
  | 0, _, _ => by simp
  | N + 1, f, hf => by
    rw [eq_sum_X_mul_quot (f := f) (by simpa using hf 0 (by simp)), pow_succ']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩)
      (mem_vars_pow N fun e he => ?_)
    rw [coeff_quot]
    split_ifs
    · exact hf _ (by rw [map_add, Finsupp.degree_single]; omega)
    · rfl

/-- `f` minus its truncation in total degree `< N` lies in `(T₁, …, Tₙ)ᴺ`. -/
lemma sub_truncTotal_mem (N : ℕ) (f : MvPowerSeries (Fin n) R) :
    f - (truncTotal N f : MvPowerSeries (Fin n) R) ∈ vars R n ^ N :=
  mem_vars_pow N fun d hd => by
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]

end Vars

section Local

variable [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]

/-! ### The evaluation -/

omit [IsAdicComplete (maximalIdeal V) V] in
lemma hasEval {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) : MvPowerSeries.HasEval a :=
  ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (ha i), by simp⟩

/-- Evaluation at `a ∈ 𝔪ⁿ`: the `V`-algebra homomorphism `V⟦T₁, …, Tₙ⟧ → V`, `T ↦ a`. -/
noncomputable def eval {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) :
    MvPowerSeries (Fin n) V →ₐ[V] V :=
  MvPowerSeries.aeval (hasEval ha)

lemma eval_X {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) (i : Fin n) :
    eval ha (MvPowerSeries.X i) = a i := by
  simp [eval, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]



/-! ### The kernel of the evaluation -/

section Kernel

open MvPowerSeries

/-- The ideal `(T₁ − a₁, …, Tₙ − aₙ)`. -/
noncomputable def ker (a : Fin n → V) : Ideal (MvPowerSeries (Fin n) V) :=
  Ideal.span (Set.range fun i => X i - C (a i))

omit [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] in
lemma algebraMap_quot (J : Ideal (MvPowerSeries (Fin n) V)) (v : V) :
    algebraMap V (MvPowerSeries (Fin n) V ⧸ J) v = Ideal.Quotient.mk J (C v) := by
  rw [IsScalarTower.algebraMap_apply V (MvPowerSeries (Fin n) V), Ideal.Quotient.algebraMap_eq,
    ← c_eq_algebraMap]

omit [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] in
lemma mk_coe {a : Fin n → V} (p : MvPolynomial (Fin n) V) :
    Ideal.Quotient.mk (ker a) (p : MvPowerSeries (Fin n) V) =
      Ideal.Quotient.mk (ker a) (C (MvPolynomial.aeval a p)) := by
  have h : (Ideal.Quotient.mkₐ V (ker a)).comp (MvPolynomial.coeToMvPowerSeries.algHom V) =
      (Algebra.ofId V _).comp (MvPolynomial.aeval a) := MvPolynomial.algHom_ext fun i => by
    change Ideal.Quotient.mk (ker a) ((MvPolynomial.X i : MvPolynomial (Fin n) V) :
      MvPowerSeries (Fin n) V) = algebraMap V _ (MvPolynomial.aeval a (MvPolynomial.X i))
    rw [MvPolynomial.coe_X, MvPolynomial.aeval_X, algebraMap_quot, Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨i, rfl⟩
  have := congrArg (fun φ => φ p) h
  simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.ofId_apply] at this
  rw [← algebraMap_quot]
  exact this

lemma eval_C {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) (v : V) :
    eval ha (C v) = v := (eval ha).commutes v

lemma ker_le {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) :
    ker a ≤ RingHom.ker (eval ha) :=
  Ideal.span_le.2 <| by
    rintro _ ⟨i, rfl⟩
    simp [eval_X, eval_C]

omit [IsAdicComplete (maximalIdeal V) V] in
lemma X_mem (i : Fin n) : (X i : MvPowerSeries (Fin n) V) ∈ maximalIdeal _ := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    constantCoeff_X]
  exact not_isUnit_zero

omit [IsAdicComplete (maximalIdeal V) V] in
lemma C_mem {v : V} (hv : v ∈ maximalIdeal V) :
    (C v : MvPowerSeries (Fin n) V) ∈ maximalIdeal _ := by
  rwa [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    constantCoeff_C]

omit [IsAdicComplete (maximalIdeal V) V] in
lemma C_mem_pow {v : V} {N : ℕ} (hv : v ∈ maximalIdeal V ^ N) :
    (C v : MvPowerSeries (Fin n) V) ∈ maximalIdeal _ ^ N := by
  have h := Ideal.mem_map_of_mem (C : V →+* MvPowerSeries (Fin n) V) hv
  rw [Ideal.map_pow] at h
  refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => ?_) N h
  exact C_mem hx

lemma eval_mem_pow {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) {N : ℕ}
    {r : MvPowerSeries (Fin n) V} (hr : r ∈ vars V n ^ N) : eval ha r ∈ maximalIdeal V ^ N := by
  have h := Ideal.mem_map_of_mem (eval ha) hr
  rw [Ideal.map_pow, vars, Ideal.map_span] at h
  refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) N h
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  simpa [eval_X] using ha i

/-- `f ≡ f(a)` modulo `(T₁ − a₁, …, Tₙ − aₙ)`. -/
theorem sub_C_eval_mem [IsNoetherianRing V] {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V)
    (f : MvPowerSeries (Fin n) V) : f - C (eval ha f) ∈ ker a := by
  by_contra h
  have hne : ker a ≠ ⊤ := fun h' => by
    have := ker_le ha (h' ▸ Submodule.mem_top : (1 : MvPowerSeries (Fin n) V) ∈ ker a)
    simp at this
  obtain ⟨N, hN⟩ := Folder100.Baire.exists_notMem_sup_pow hne h
  apply hN
  set p : MvPolynomial (Fin n) V := truncTotal N f
  have hr := sub_truncTotal_mem N f
  have hp : (p : MvPowerSeries (Fin n) V) - C (MvPolynomial.aeval a p) ∈ ker a :=
    Ideal.Quotient.eq.1 (mk_coe p)
  have hev : MvPolynomial.aeval a p - eval ha f ∈ maximalIdeal V ^ N := by
    have := neg_mem (eval_mem_pow ha hr)
    rwa [map_sub, eval, MvPowerSeries.aeval_coe, neg_sub] at this
  have hvars : vars V n ^ N ≤ maximalIdeal (MvPowerSeries (Fin n) V) ^ N :=
    Ideal.pow_right_mono (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact X_mem i)) N
  have e : f - C (eval ha f) = ((p : MvPowerSeries (Fin n) V) - C (MvPolynomial.aeval a p)) +
      ((f - (p : MvPowerSeries (Fin n) V)) + C (MvPolynomial.aeval a p - eval ha f)) := by
    rw [map_sub]; ring
  rw [e]
  exact add_mem (Ideal.mem_sup_left hp)
    (Ideal.mem_sup_right (add_mem (hvars hr) (C_mem_pow hev)))

variable [IsNoetherianRing V]

/-- The kernel of the evaluation at `a` is `(T₁ − a₁, …, Tₙ − aₙ)`. -/
theorem ker_eval {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) :
    RingHom.ker (eval ha) = ker a := by
  refine le_antisymm (fun f hf => ?_) (ker_le ha)
  have := sub_C_eval_mem ha f
  rwa [RingHom.mem_ker.1 hf, map_zero, sub_zero] at this

omit [IsNoetherianRing V] in
lemma eval_surjective {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) :
    Function.Surjective (eval ha) := fun v => ⟨C v, eval_C ha v⟩

/-- `V⟦T₁, …, Tₙ⟧ ⧸ (T₁ − a₁, …, Tₙ − aₙ) ≃ V`. -/
noncomputable def quotEquiv {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) :
    (MvPowerSeries (Fin n) V ⧸ ker a) ≃ₐ[V] V :=
  (Ideal.quotientEquivAlgOfEq V (ker_eval ha).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (eval_surjective ha))

/-- **The parametrisation.** A `V`-algebra homomorphism `φ : V⟦T₁, …, Tₙ⟧ → V` with
`φ(Tᵢ) ∈ 𝔪` is the evaluation at `a = (φ(T₁), …, φ(Tₙ))`. -/
theorem eq_eval (φ : MvPowerSeries (Fin n) V →ₐ[V] V) (hφ : ∀ i, φ (X i) ∈ maximalIdeal V) :
    φ = eval hφ := by
  ext f
  have hle : ker (fun i => φ (X i)) ≤ RingHom.ker φ := Ideal.span_le.2 <| by
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (φ.commutes _).symm
  have := hle (sub_C_eval_mem hφ f)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  rw [this]
  exact (φ.commutes _).trans rfl

/-- A local `V`-algebra homomorphism `V⟦T₁, …, Tₙ⟧ → V` is an evaluation at a point of `𝔪ⁿ`. -/
theorem exists_eq_eval (φ : MvPowerSeries (Fin n) V →ₐ[V] V) [IsLocalHom φ] :
    ∃ (a : Fin n → V) (ha : ∀ i, a i ∈ maximalIdeal V), φ = eval ha :=
  ⟨fun i => φ (X i), fun i h => X_mem i (isUnit_of_map_unit φ _ h), eq_eval φ _⟩

omit [IsNoetherianRing V] in
/-- Distinct points of `𝔪ⁿ` give distinct evaluations. -/
theorem eval_injective {a b : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V)
    (hb : ∀ i, b i ∈ maximalIdeal V) (h : eval ha = eval hb) : a = b :=
  funext fun i => by rw [← eval_X ha i, h, eval_X]

/-- Points of `𝔪ⁿ` congruent modulo `𝔪ᴺ` have values congruent modulo `𝔪ᴺ`. -/
theorem eval_sub_eval_mem {a b : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V)
    (hb : ∀ i, b i ∈ maximalIdeal V) {N : ℕ} (hab : ∀ i, b i - a i ∈ maximalIdeal V ^ N)
    (f : MvPowerSeries (Fin n) V) : eval hb f - eval ha f ∈ maximalIdeal V ^ N := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (sub_C_eval_mem ha f)
  have := congrArg (eval hb) hc
  rw [map_sub, eval_C, map_sum] at this
  rw [← this]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [map_mul, map_sub, eval_X, eval_C]
  exact Ideal.mul_mem_left _ _ (hab i)

omit [IsNoetherianRing V] in
lemma eval_congr {a b : Fin n → V} (h : a = b) (ha : ∀ i, a i ∈ maximalIdeal V)
    (hb : ∀ i, b i ∈ maximalIdeal V) : eval ha = eval hb := by
  subst h; rfl

end Kernel

/-! ### Neighbourhoods in `Vⁿ` -/

/-- `𝔪ⁿ ⊂ Vⁿ`. -/
def cube (V : Type*) [CommRing V] [IsLocalRing V] (n : ℕ) : Set (Fin n → V) :=
  {a | ∀ i, a i ∈ maximalIdeal V}

/-- The neighbourhood `a + (𝔪ᴹ)ⁿ` of `a`. -/
def nbhd (a : Fin n → V) (M : ℕ) : Set (Fin n → V) :=
  {b | ∀ i, b i - a i ∈ maximalIdeal V ^ M}

omit [IsAdicComplete (maximalIdeal V) V] in
lemma isOpen_nbhd (a : Fin n → V) (M : ℕ) : IsOpen (nbhd a M) := by
  simp only [nbhd, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_pow M).preimage ((continuous_apply i).sub continuous_const)

omit [IsAdicComplete (maximalIdeal V) V] in
lemma exists_nbhd_subset {a : Fin n → V} {U : Set (Fin n → V)} (hU : U ∈ 𝓝 a) :
    ∃ M, nbhd a M ⊆ U := by
  rw [nhds_pi] at hU
  obtain ⟨⟨I, M⟩, -, hsub⟩ :=
    (Filter.hasBasis_pi fun i => isAdic.hasBasis_nhds (a i)).mem_iff.1 hU
  refine ⟨∑ i, M i, fun b hb => hsub fun i _ => ⟨b i - a i, Ideal.pow_le_pow_right
    (Finset.single_le_sum (fun j _ => Nat.zero_le (M j)) (Finset.mem_univ i)) (hb i),
    add_sub_cancel _ _⟩⟩

omit [IsAdicComplete (maximalIdeal V) V] in
/-- `𝔪ⁿ` is open in `Vⁿ`. -/
lemma isOpen_cube : IsOpen (cube V n) := by
  have : cube V n = nbhd 0 1 := by ext; simp [cube, nbhd]
  exact this ▸ isOpen_nbhd 0 1

end Local

/-! ### The zero set of a series: closed, with empty interior -/

section Zero

open MvPowerSeries

variable [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]

/-- The evaluation `V⟦T⟧ → V` at `c ∈ 𝔪`, through `Folder100.quotEquiv`. -/
noncomputable def eval₁ {c : V} (hc : c ∈ maximalIdeal V) : V⟦X⟧ →ₐ[V] V :=
  (Folder100.quotEquiv hc).toAlgHom.comp (Ideal.Quotient.mkₐ V _)

lemma eval₁_eq_zero_iff {c : V} (hc : c ∈ maximalIdeal V) (g : V⟦X⟧) :
    eval₁ hc g = 0 ↔ g ∈ Ideal.span {PowerSeries.X - PowerSeries.C c} := by
  rw [eval₁, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    map_eq_zero_iff _ (AlgEquiv.injective _), Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]

lemma eval₁_C {c : V} (hc : c ∈ maximalIdeal V) (v : V) : eval₁ hc (PowerSeries.C v) = v :=
  (eval₁ hc).commutes v

lemma eval₁_X {c : V} (hc : c ∈ maximalIdeal V) : eval₁ hc PowerSeries.X = c := by
  have h : PowerSeries.X - PowerSeries.C c ∈ RingHom.ker (eval₁ hc) :=
    (eval₁_eq_zero_iff hc _).2 (Ideal.mem_span_singleton_self _)
  rw [RingHom.mem_ker, map_sub, eval₁_C, sub_eq_zero] at h
  exact h

/-- Evaluation at `(c, b)` is evaluation at `c` of the series `f(T₀, b)` of `V⟦T₀⟧`. -/
lemma eval_cons {c : V} (hc : c ∈ maximalIdeal V) {b : Fin n → V}
    (hb : ∀ i, b i ∈ maximalIdeal V) (hcb : ∀ i, (Fin.cons c b : Fin (n + 1) → V) i ∈
      maximalIdeal V) (f : MvPowerSeries (Fin (n + 1)) V) :
    eval hcb f = eval₁ hc (PowerSeries.map (eval hb).toRingHom (finSuccEquiv V n f)) := by
  let ψ := (eval₁ hc).comp ((PowerSeries.mapAlgHom (eval hb)).comp (finSuccEquiv V n).toAlgHom)
  have hψ : ∀ i, ψ (X i) = (Fin.cons c b : Fin (n + 1) → V) i := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ψ, finSuccEquiv_X_zero, PowerSeries.mapAlgHom_apply, PowerSeries.map_X, eval₁_X]
    · simp [ψ, finSuccEquiv_X_succ, PowerSeries.mapAlgHom_apply, PowerSeries.map_C, eval₁_C,
        eval_X]
  have hψ' : ∀ i, ψ (X i) ∈ maximalIdeal V := fun i => hψ i ▸ hcb i
  rw [eval_congr (funext hψ).symm hcb hψ', ← eq_eval ψ hψ']
  rfl

/-- **The identity principle.** A series vanishing on a product of infinite subsets of `𝔪` is
zero (induction on `n`, from the finiteness of the zeros of a one-variable series,
`Folder100.finite_bad`). -/
theorem eq_zero_of_eval_eq_zero : ∀ {n : ℕ} (S : Fin n → Set V),
    (∀ i, S i ⊆ maximalIdeal V) → (∀ i, (S i).Infinite) → ∀ f : MvPowerSeries (Fin n) V,
    (∀ (a : Fin n → V) (ha : ∀ i, a i ∈ maximalIdeal V), (∀ i, a i ∈ S i) → eval ha f = 0) →
    f = 0
  | 0, _, _, _, f, hf => by
    have ha : ∀ i : Fin 0, (Fin.elim0 i : V) ∈ maximalIdeal V := fun i => i.elim0
    have h1 := sub_C_eval_mem ha f
    rw [hf _ ha (fun i => i.elim0), map_zero, sub_zero] at h1
    simpa [ker] using h1
  | n + 1, S, hS, hSi, f, hf => by
    apply (finSuccEquiv V n).injective
    rw [map_zero]
    refine PowerSeries.ext fun k => ?_
    rw [map_zero]
    refine eq_zero_of_eval_eq_zero (fun i => S i.succ) (fun i => hS _) (fun i => hSi _) _
      fun b hb hbS => ?_
    have hg : PowerSeries.map (eval hb).toRingHom (finSuccEquiv V n f) = 0 := by
      by_contra hne
      apply hSi 0
      refine (Folder100.finite_bad hne).subset fun c hc => ⟨hS 0 hc, ?_⟩
      have hcb : ∀ i, (Fin.cons c b : Fin (n + 1) → V) i ∈ maximalIdeal V :=
        fun i => Fin.cases (hS 0 hc) hb i
      rw [← eval₁_eq_zero_iff (hS 0 hc), ← eval_cons (hS 0 hc) hb hcb]
      exact hf _ hcb fun i => Fin.cases hc hbS i
    have := congrArg (PowerSeries.coeff k) hg
    simpa using this

omit [IsAdicComplete (maximalIdeal V) V] in
lemma exists_notMem_pow {x : V} (hx : x ≠ 0) : ∃ N, x ∉ maximalIdeal V ^ N := by
  by_contra! h
  have : x ∈ ⨅ N : ℕ, maximalIdeal V ^ N := Ideal.mem_iInf.2 h
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top] at this
  exact hx this

/-- The zeros `{a ∈ 𝔪ⁿ | f(a) = 0}` of `f`. -/
def zeroSet (f : MvPowerSeries (Fin n) V) : Set (Fin n → V) :=
  {a | ∃ ha : ∀ i, a i ∈ maximalIdeal V, eval ha f = 0}

/-- The zero set of `f` is closed in `Vⁿ`. -/
theorem isClosed_zeroSet (f : MvPowerSeries (Fin n) V) : IsClosed (zeroSet f) := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun a ha => ?_)
  by_cases h : ∀ i, a i ∈ maximalIdeal V
  · have hne : eval h f ≠ 0 := fun h0 => ha ⟨h, h0⟩
    obtain ⟨N, hN⟩ := exists_notMem_pow hne
    refine ⟨nbhd a (N + 1), fun b hb => ?_, isOpen_nbhd a _, fun i => by simp⟩
    rintro ⟨hb', h0⟩
    have := eval_sub_eval_mem h hb' hb f
    rw [h0, zero_sub] at this
    exact hN (Ideal.pow_le_pow_right (Nat.le_succ N) (by simpa using this))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    refine ⟨nbhd a 1, fun b hb => ?_, isOpen_nbhd a _, fun i => by simp⟩
    rintro ⟨hb', -⟩
    have := sub_mem (hb' i) (by simpa using hb i)
    rw [sub_sub_cancel] at this
    exact hi this

/-- The zero set of `f ≠ 0` has empty interior in `Vⁿ`. -/
theorem interior_zeroSet {f : MvPowerSeries (Fin n) V} (hf : f ≠ 0) :
    interior (zeroSet f) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun a ha => hf ?_
  obtain ⟨M, hM⟩ := exists_nbhd_subset (mem_interior_iff_mem_nhds.1 ha)
  obtain ⟨ha𝔪, -⟩ := interior_subset ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : Uncountable V := Folder100.uncountable
  have hsub : maximalIdeal V ^ (M + 1) ≤ maximalIdeal V ^ M := Ideal.pow_le_pow_right M.le_succ
  refine eq_zero_of_eval_eq_zero (fun i => {x | x - a i ∈ maximalIdeal V ^ (M + 1)})
    (fun i x hx => ?_) (fun i => ?_) f fun b hb hbS => ?_
  · have := add_mem (Ideal.pow_le_self (Nat.succ_ne_zero M) hx) (ha𝔪 i)
    rwa [sub_add_cancel] at this
  · refine Set.infinite_of_injective_forall_mem (f := fun v => a i + ϖ ^ (M + 1) * v)
      (fun v w h => mul_left_cancel₀ (pow_ne_zero _ hϖ.ne_zero) (add_left_cancel h))
      fun v => ?_
    simp only [Set.mem_ofPred_eq, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖ.not_isUnit _)
  · obtain ⟨_, h⟩ := hM fun i => hsub (hbS i)
    exact h

/-- **Baire.** Countably many nonzero `fᵢ ∈ V⟦T₁, …, Tₙ⟧` have a common non-zero point
`a ∈ 𝔪ⁿ`: `Vⁿ` is complete metrisable, hence a Baire space, the zero sets are closed with empty
interior, and `𝔪ⁿ` is a nonempty open subset. -/
theorem exists_eval_ne_zero {ι : Type*} [Countable ι] (f : ι → MvPowerSeries (Fin n) V)
    (hf : ∀ i, f i ≠ 0) :
    ∃ (a : Fin n → V) (ha : ∀ i, a i ∈ maximalIdeal V), ∀ i, eval ha (f i) ≠ 0 := by
  have : (𝓝 (0 : V)).IsCountablyGenerated := isAdic.hasBasis_nhds_zero.isCountablyGenerated
  have : (uniformity V).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have hd : Dense (⋂ i, (zeroSet (f i))ᶜ) :=
    dense_iInter_of_isOpen (fun i => (isClosed_zeroSet _).isOpen_compl)
      fun i => interior_eq_empty_iff_dense_compl.1 (interior_zeroSet (hf i))
  obtain ⟨a, ha, haZ⟩ := hd.inter_open_nonempty (cube V n) isOpen_cube
    ⟨0, fun i => zero_mem _⟩
  exact ⟨a, ha, fun i h => Set.mem_iInter.1 haZ i ⟨ha, h⟩⟩

end Zero

/-! ### Points of dimension one -/

section Points

open MvPowerSeries

lemma coheight_eq_one {α : Type*} [PartialOrder α] {x : α} (h1 : ¬ IsMax x)
    (h2 : ∀ y > x, IsMax y) : Order.coheight x = 1 := by
  refine le_antisymm (Order.coheight_le_coe_iff.2 fun y hy => ?_)
    (Order.one_le_iff_ne_zero.2 (Order.coheight_ne_zero.2 h1))
  rw [Order.coheight_eq_zero.2 (h2 y hy)]
  exact zero_lt_one

lemma isMax_iff {A : Type*} [CommRing A] (x : PrimeSpectrum A) :
    IsMax x ↔ x.asIdeal.IsMaximal := by
  refine ⟨fun h => ?_, fun h y hy => (h.eq_of_le y.2.ne_top hy).ge⟩
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal _ x.2.ne_top
  have : x.asIdeal = M :=
    le_antisymm hxM (h (b := ⟨M, hM.isPrime⟩) (show x ≤ ⟨M, hM.isPrime⟩ from hxM))
  exact this ▸ hM

/-- A point of `Spec A` of coheight one: it is not closed, and every point specialising it
strictly is closed. -/
lemma coheight_eq_one_of_isMaximal {A : Type*} [CommRing A] (x : PrimeSpectrum A)
    (h1 : ¬ x.asIdeal.IsMaximal) (h2 : ∀ q : Ideal A, q.IsPrime → x.asIdeal < q → q.IsMaximal) :
    Order.coheight x = 1 :=
  coheight_eq_one ((isMax_iff x).not.2 h1) fun y hy => (isMax_iff y).2 (h2 _ y.2 hy)

variable [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]

lemma isPrime_ker {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) : (ker a).IsPrime :=
  ker_eval ha ▸ RingHom.ker_isPrime _

lemma not_isMaximal_ker {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) :
    ¬ (ker a).IsMaximal := fun h => IsDiscreteValuationRing.not_isField V <|
  MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 h)
    (quotEquiv ha).toRingEquiv.symm.toMulEquiv

/-- A prime strictly above `(T₁ − a₁, …, Tₙ − aₙ)` is maximal: `V` has dimension one. -/
lemma isMaximal_of_ker_lt {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) {q : Ideal _}
    [q.IsPrime] (hq : ker a < q) : q.IsMaximal := by
  have hk : RingHom.ker (eval ha) ≤ q := (ker_eval ha).le.trans hq.le
  have hc : (q.map (eval ha)).comap (eval ha) = q := by
    rw [Ideal.comap_map_of_surjective _ (eval_surjective ha), ← RingHom.ker_eq_comap_bot,
      sup_eq_left.2 hk]
  have : (q.map (eval ha)).IsPrime := Ideal.map_isPrime_of_surjective (eval_surjective ha) hk
  have hne : q.map (eval ha) ≠ ⊥ := fun h => by
    rw [h, ← RingHom.ker_eq_comap_bot, ker_eval ha] at hc
    exact hq.ne hc
  have := IsPrime.to_maximal_ideal (hpi := this) hne
  rw [← hc]
  exact Ideal.comap_isMaximal_of_surjective _ (eval_surjective ha)

/-- The point `(T₁ − a₁, …, Tₙ − aₙ)` of `Spec V⟦T₁, …, Tₙ⟧` has coheight one:
`dim closure {x} = 1`. -/
theorem coheight_ker {a : Fin n → V} (ha : ∀ i, a i ∈ maximalIdeal V) :
    Order.coheight (⟨ker a, isPrime_ker ha⟩ : PrimeSpectrum (MvPowerSeries (Fin n) V)) = 1 :=
  coheight_eq_one_of_isMaximal _ (not_isMaximal_ker ha) fun _ _ h => isMaximal_of_ker_lt ha h

/-- **The several-variable `exists_avoid`.** Countably many nonzero `fᵢ ∈ V⟦T₁, …, Tₙ⟧` lie
outside the kernel `𝔭` of the evaluation at some `a ∈ 𝔪ⁿ`: `𝔭` is a prime with
`V⟦T₁, …, Tₙ⟧ ⧸ 𝔭 ≃ V`, a point of dimension one of `Spec V⟦T₁, …, Tₙ⟧` outside every
`V(fᵢ)`. -/
theorem exists_avoid {ι : Type*} [Countable ι] (f : ι → MvPowerSeries (Fin n) V)
    (hf : ∀ i, f i ≠ 0) :
    ∃ (a : Fin n → V) (ha : ∀ i, a i ∈ maximalIdeal V),
      Nonempty ((MvPowerSeries (Fin n) V ⧸ ker a) ≃ₐ[V] V) ∧
      Order.coheight (⟨ker a, isPrime_ker ha⟩ : PrimeSpectrum (MvPowerSeries (Fin n) V)) = 1 ∧
      ∀ i, f i ∉ ker a := by
  obtain ⟨a, ha, h⟩ := exists_eval_ne_zero f hf
  exact ⟨a, ha, ⟨quotEquiv ha⟩, coheight_ker ha, fun i hi => h i (ker_le ha hi)⟩

/-- **Lifting along a finite extension.** Let `R` be a domain, integral over
`Θ = V⟦T₁, …, Tₙ⟧` with `Θ → R` injective (by Cohen's theorem, any complete noetherian local
domain is finite over such a `Θ` when `V` can be taken to be a discrete valuation ring).
Countably many nonzero `gᵢ ∈ R` lie outside some prime `Q` of coheight one: the norm-like
multiples `aᵢ ∈ Θ ∩ gᵢR` are nonzero, `exists_avoid` gives `𝔭`, and `Q` lies over `𝔭`. -/
theorem exists_avoid_of_isIntegral {R : Type*} [CommRing R] [IsDomain R]
    [Algebra (MvPowerSeries (Fin n) V) R] [Algebra.IsIntegral (MvPowerSeries (Fin n) V) R]
    (hinj : Function.Injective (algebraMap (MvPowerSeries (Fin n) V) R)) {ι : Type*}
    [Countable ι] (g : ι → R) (hg : ∀ i, g i ≠ 0) :
    ∃ Q : PrimeSpectrum R, Order.coheight Q = 1 ∧ ∀ i, g i ∉ Q.asIdeal := by
  have hb : ∀ i, ∃ c : MvPowerSeries (Fin n) V, c ≠ 0 ∧ algebraMap _ R c ∈ Ideal.span {g i} :=
    fun i => by
    have := Ideal.under_ne_bot_of_integral_mem (hg i) (Ideal.mem_span_singleton_self (g i))
      (Algebra.IsIntegral.isIntegral (R := MvPowerSeries (Fin n) V) (g i))
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨c, hc0, hc⟩
  choose c hc0 hc using hb
  obtain ⟨a, ha, -, -, hca⟩ := exists_avoid c hc0
  have := isPrime_ker ha
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (ker a) ⊥
    (by
      rw [Ideal.under, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le)
  refine ⟨⟨Q, hQ⟩, coheight_eq_one_of_isMaximal _ (fun h => not_isMaximal_ker ha ?_)
    fun q _ hq => ?_, fun i hi => hca i ?_⟩
  · rw [← hQP]
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  · refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under q (isMaximal_of_ker_lt ha ?_)
    rw [← hQP]
    exact Ideal.IsIntegral.under_lt_under hq
  · rw [← hQP]
    exact (Ideal.span_singleton_le_iff_mem _).2 hi (hc i)

/-- **Corollary of page 38, through `V⟦T₁, …, Tₙ⟧`.** In `Spec R`, `R` a domain integral over
`V⟦T₁, …, Tₙ⟧` (injectively), countably many proper closed subsets miss some point of
coheight one. -/
theorem exists_coheight_eq_one_of_isIntegral {R : Type*} [CommRing R] [IsDomain R]
    [Algebra (MvPowerSeries (Fin n) V) R] [Algebra.IsIntegral (MvPowerSeries (Fin n) V) R]
    (hinj : Function.Injective (algebraMap (MvPowerSeries (Fin n) V) R)) {ι : Type*}
    [Countable ι] (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hZu : ∀ i, Z i ≠ Set.univ) :
    ∃ x : PrimeSpectrum R, Order.coheight x = 1 ∧ ∀ i, x ∉ Z i := by
  have hZI : ∀ i (x : PrimeSpectrum R), x ∈ Z i ↔ PrimeSpectrum.vanishingIdeal (Z i) ≤ x.asIdeal :=
    fun i x => by
      rw [← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus,
        PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, (hZ i).closure_eq]
  have hg : ∀ i, ∃ g ∈ PrimeSpectrum.vanishingIdeal (Z i), g ≠ 0 := fun i =>
    Submodule.exists_mem_ne_zero_of_ne_bot fun h => hZu i <| Set.eq_univ_of_forall fun x =>
      (hZI i x).2 (h ▸ bot_le)
  choose g hgZ hg0 using hg
  obtain ⟨x, hx, hxg⟩ := exists_avoid_of_isIntegral hinj g hg0
  exact ⟨x, hx, fun i hi => hxg i ((hZI i x).1 hi (hgZ i))⟩

end Points

end Grothendieck.Folder100Baire
