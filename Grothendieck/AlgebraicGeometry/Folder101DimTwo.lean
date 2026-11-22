/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
import Grothendieck.Attr

/-!
# Folder 101, pages 14–15: local duality with algebraic Matlis duals fails in dimension 2

Finding `101-sheaf-duality-dim-two-fails`. Pages 10 to 15 of folder 101 test local duality for
arbitrary (not quasi-coherent) `O_X`-modules on `X = Spec A`, `A` complete regular local. In
dimension 1 it holds (`Grothendieck/AlgebraicGeometry/Folder101.lean`, `Folder101Ext.lean`,
`Folder101LocalCohomology.lean`). In dimension 2, for `f ∈ 𝔪` non-zero, `U = X_f` and
`F = j_!O_U`, the page computes `Ext⁰(X; F, O_X) = A_f` and the duality map
`φ : A_f → D(H²_x(F)) = Hom_A(H²_x(F), E(k))`, and concludes « φ est injection » and
« φ n'est pas surjective »; no proof of the second assertion is on the page.

## Main results

For `A = k⟦x⟧⟦y⟧` (that is `k[[x, y]]`) and `f = x`, the module `A_x` is not isomorphic, as an
`A`-module, to any Matlis-type dual `Hom_A(H, E)` with `E` injective, whatever the module `H`
(`not_nonempty_linearEquiv_dual`). Hence every injective `A`-linear map `A_x → Hom_A(H, E)` fails
to be surjective (`not_surjective_of_injective`); applied to `H = H²_x(j_!O_U)`, `E = E(k)` and
the page's injective map `φ`, this is the page's doubly underlined « φ n'est pas surjective ».
The result is proved more generally for `A = R⟦y⟧`, `R` a domain, `x = r ∈ R` non-zero and not a
unit (`not_telescopeSurj_away`, `not_nonempty_linearEquiv_dual_powerSeries`).

## Implementation notes

The invariant is the property `TelescopeSurj y N`: every sequence `(aᵢ)` of `N` is of the form
`aᵢ = nᵢ - y nᵢ₊₁` (i.e. `lim¹` of `⋯ →y N →y N` vanishes, a form of `Ext¹_A(A_y, N) = 0`:
`Hom_A(H, E)` is « `y`-cotorsion »).
* `telescopeSurj_dual`: `Hom_A(H, E)` has it for every `y`, every `H` and every injective `E`.
  The telescope `T : ⊕ᵢ H → ⊕ᵢ H`, `T(h)ᵢ = hᵢ - y hᵢ₋₁`, is injective (`telescope_injective`),
  and maps `⊕ᵢ H → E` extend along it; reading the extension on each summand gives `(nᵢ)`.
* `not_telescopeSurj_away`: `A_x` fails it for `y` on the sequence `aᵢ = x⁻ⁱ`. A solution gives
  `n₀ = ∑_{i<N} (y/x)ⁱ + y^N n_N` for every `N`; clearing denominators (`n₀ = b/x^m`) and
  reading the coefficient of `y^{m+1}` with `N = m + 2` gives `b_{m+1} r = 1`, so `r` would be a
  unit. This is the finding's sketch: `A_x` « is not complete in the `y`-direction », the
  height-one localisation `A_(y)` (with `x ∉ (y)`) not being complete, whereas a Matlis dual is.

## Not formalised

Part of the sheaf side: `j_!O_U`, `Ext⁰(X; j_!O_U, O_X) = A_f` and the
reduction of `H^i_x(j_!O_U)` to the cohomology of the punctured spectrum are in
`Grothendieck/AlgebraicGeometry/Folder101Sheaf.lean`; the computation of `H¹(X ∖ {x}, j_!O_U)`,
the exact sequence `0 → A → ∏ O_{x_i} → H²_x(F) → E(k) → 0` and the map `φ` itself; hence also the
page's injectivity of `φ` (only « injective ⇒ not surjective » is proved, for every injective map).
The identification of `TelescopeSurj` with `Ext¹_A(A_y, -) = 0` for mathlib's `Ext`; the general
claim for every complete regular local ring of dimension 2 and every `f`; the identification of
`k⟦x⟧⟦y⟧` with the two-variable `MvPowerSeries`; the page's topological-dual repair (page 15).

## References

* A. Grothendieck, cote 101, pp. 10–15 (finding `101-sheaf-duality-dim-two-fails`)
* Stacks Project, tag 03DI
-/

@[expose] public section


namespace Grothendieck.Folder101DimTwo

open PowerSeries

universe u v

section Dual

variable {A : Type u} [CommRing A]

/-- The telescope property for `y`: every sequence `(aᵢ)` of `N` is `(nᵢ - y nᵢ₊₁)` for some
sequence `(nᵢ)` of `N`. -/
def TelescopeSurj (y : A) (N : Type*) [AddCommGroup N] [Module A N] : Prop :=
  ∀ a : ℕ → N, ∃ n : ℕ → N, ∀ i, n i - y • n (i + 1) = a i

/-- The property is invariant under `A`-linear isomorphism. -/
lemma TelescopeSurj.of_linearEquiv {y : A} {N N' : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (e : N ≃ₗ[A] N') (h : TelescopeSurj y N) :
    TelescopeSurj y N' := by
  intro a
  obtain ⟨n, hn⟩ := h fun i => e.symm (a i)
  refine ⟨fun i => e (n i), fun i => ?_⟩
  rw [← map_smul, ← map_sub, hn, LinearEquiv.apply_symm_apply]

variable (H : Type v) [AddCommGroup H] [Module A H]

/-- The telescope `T : ⊕ᵢ H → ⊕ᵢ H`, `T(h)ᵢ = hᵢ - y hᵢ₋₁`. -/
noncomputable def telescope (y : A) : (ℕ →₀ H) →ₗ[A] (ℕ →₀ H) :=
  LinearMap.id - y • Finsupp.lmapDomain H A Nat.succ

lemma telescope_single (y : A) (i : ℕ) (h : H) :
    telescope H y (Finsupp.single i h) = Finsupp.single i h - Finsupp.single (i + 1) (y • h) := by
  simp [telescope, Finsupp.lmapDomain, Finsupp.mapDomain_single, Finsupp.smul_single]

/-- The telescope is injective, for every module `H` and every `y`. -/
theorem telescope_injective (y : A) : Function.Injective (telescope H y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  have key : ∀ i, h i = y • (Finsupp.mapDomain Nat.succ h) i := by
    intro i
    have := congrArg (fun g : ℕ →₀ H => g i) hh
    simp only [telescope, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, Finsupp.coe_zero,
      Pi.zero_apply, sub_eq_zero] at this
    exact this
  ext i
  induction i with
  | zero =>
    change h 0 = 0
    rw [key, Finsupp.mapDomain_of_notMem_range _ _ (by simp), smul_zero]
  | succ i ih =>
    change h (i + 1) = 0
    rw [key, Finsupp.mapDomain_apply_of_injective Nat.succ_injective, show h i = 0 from ih,
      smul_zero]

/-- **Matlis duals have the telescope property.** For every module `H`, every injective module
`E` and every `y`, `Hom_A(H, E)` satisfies `TelescopeSurj y`. -/
theorem telescopeSurj_dual (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective A E]
    (y : A) : TelescopeSurj y (H →ₗ[A] E) := by
  intro a
  obtain ⟨g, hg⟩ := Module.Injective.out (telescope H y) (telescope_injective H y)
    (Finsupp.lsum A a)
  refine ⟨fun i => g ∘ₗ Finsupp.lsingle i, fun i => ?_⟩
  ext h
  have := hg (Finsupp.single i h)
  rw [telescope_single, map_sub, Finsupp.lsum_single] at this
  simpa [← map_smul] using this

end Dual

section PowerSeries

/-- `xⁱ` as an element of the submonoid of powers of `x`. -/
def powElt {A : Type u} [CommRing A] (x : A) (i : ℕ) : Submonoid.powers x :=
  ⟨x ^ i, pow_mem (Submonoid.mem_powers x) i⟩

@[simp] lemma powElt_coe {A : Type u} [CommRing A] (x : A) (i : ℕ) : (powElt x i : A) = x ^ i :=
  rfl

variable {R : Type u} [CommRing R] [IsDomain R]

/-- **`A_x` fails the telescope property for `y`**, for `A = R⟦y⟧` and `x = r ∈ R` non-zero and not
a unit: the sequence `aᵢ = x⁻ⁱ` is not of the form `(nᵢ - y nᵢ₊₁)`. -/
theorem not_telescopeSurj_away {r : R} (hr0 : r ≠ 0) (hr : ¬IsUnit r) :
    ¬TelescopeSurj (X : R⟦X⟧) (Localization.Away (C r : R⟦X⟧)) := by
  set x : R⟦X⟧ := C r with hx
  intro hT
  obtain ⟨n, hn⟩ := hT fun i => IsLocalization.mk' (Localization.Away x) (1 : R⟦X⟧) (powElt x i)
  -- the telescoped identity `n₀ = ∑_{i<N} yⁱ aᵢ + y^N n_N`
  have tele : ∀ N, n 0 = ∑ i ∈ Finset.range N, (X : R⟦X⟧) ^ i •
      IsLocalization.mk' (Localization.Away x) (1 : R⟦X⟧) (powElt x i) + (X : R⟦X⟧) ^ N • n N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [ih, Finset.sum_range_succ, ← hn N, smul_sub, pow_succ, mul_smul]
      abel
  have hx0 : x ≠ 0 := fun h => hr0 (by simpa [hx] using congrArg (coeff 0) h)
  have hinj : Function.Injective (algebraMap R⟦X⟧ (Localization.Away x)) :=
    IsLocalization.injective (Localization.Away x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  obtain ⟨⟨b, s⟩, hb⟩ := IsLocalization.surj (Submonoid.powers x) (n 0)
  obtain ⟨m, hm⟩ := s.prop
  set N := m + 2 with hN
  obtain ⟨⟨c, t⟩, hc⟩ := IsLocalization.surj (Submonoid.powers x) (n N)
  obtain ⟨p, hp⟩ := t.prop
  simp only [← hm, map_pow] at hb
  simp only [← hp, map_pow] at hc
  -- clear denominators: an identity in `A = R⟦X⟧`
  have hA : b * x ^ (p + N) = ∑ i ∈ Finset.range N, X ^ i * x ^ (m + p + (N - i)) +
      X ^ N * (c * x ^ (m + N)) := by
    apply hinj
    have hsum : ∀ i ∈ Finset.range N,
        algebraMap R⟦X⟧ (Localization.Away x) (X ^ i * x ^ (m + p + (N - i))) =
          (X : R⟦X⟧) ^ i • IsLocalization.mk' (Localization.Away x) (1 : R⟦X⟧) (powElt x i) *
            algebraMap R⟦X⟧ (Localization.Away x) x ^ (m + p + N) := by
      intro i hi
      have hiN : i ≤ N := (Finset.mem_range.1 hi).le
      have hs := IsLocalization.mk'_spec (Localization.Away x) (1 : R⟦X⟧) (powElt x i)
      rw [powElt_coe, map_one, map_pow] at hs
      rw [Algebra.smul_def]
      simp only [map_mul, map_pow]
      rw [show m + p + N = i + (m + p + (N - i)) by omega, pow_add]
      linear_combination (-(algebraMap R⟦X⟧ (Localization.Away x) X ^ i *
        algebraMap R⟦X⟧ (Localization.Away x) x ^ (m + p + (N - i)))) * hs
    have t := tele N
    rw [Algebra.smul_def (X ^ N), map_pow] at t
    rw [map_add, map_sum, Finset.sum_congr rfl hsum, ← Finset.sum_mul]
    simp only [map_mul, map_pow]
    linear_combination (-(algebraMap R⟦X⟧ (Localization.Away x) x ^ (p + N))) * hb +
      (algebraMap R⟦X⟧ (Localization.Away x) X ^ N *
        algebraMap R⟦X⟧ (Localization.Away x) x ^ (m + N)) * hc +
      algebraMap R⟦X⟧ (Localization.Away x) x ^ (m + p + N) * t
  -- read the coefficient of `y^(m+1)`
  have hcoeff := congrArg (coeff (m + 1)) hA
  simp only [hx, ← map_pow, coeff_mul_C, map_add, map_sum] at hcoeff
  rw [coeff_X_pow_mul'] at hcoeff
  simp only [show ¬N ≤ m + 1 by omega, ↓reduceIte, add_zero] at hcoeff
  have hterm : ∀ i ∈ Finset.range N, coeff (m + 1) ((X : R⟦X⟧) ^ i) * r ^ (m + p + (N - i)) =
      if m + 1 = i then r ^ (m + p + 1) else 0 := by
    intro i _
    rw [coeff_X_pow]
    split_ifs with h
    · subst h
      rw [one_mul, show N - (m + 1) = 1 by omega]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq] at hcoeff
  simp only [Finset.mem_range, show m + 1 < N by omega, ↓reduceIte] at hcoeff
  have hsplit : coeff (m + 1) b * r ^ (p + N) = r ^ (m + p + 1) * (r * coeff (m + 1) b) := by
    rw [show p + N = m + p + 1 + 1 by omega, pow_succ]; ring
  have key : r ^ (m + p + 1) * (r * coeff (m + 1) b) = r ^ (m + p + 1) * 1 := by
    rw [← hsplit, hcoeff, mul_one]
  exact hr (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ (pow_ne_zero _ hr0) key))

/-- For `A = R⟦y⟧`, `x = r` as in `not_telescopeSurj_away`, `A_x` is not isomorphic to any
`Hom_A(H, E)` with `E` injective. -/
@[montpellier "101, 14–15"]
theorem not_nonempty_linearEquiv_dual_powerSeries {r : R} (hr0 : r ≠ 0) (hr : ¬IsUnit r)
    (H E : Type v) [AddCommGroup H] [Module R⟦X⟧ H] [AddCommGroup E] [Module R⟦X⟧ E]
    [Module.Injective R⟦X⟧ E] :
    ¬Nonempty (Localization.Away (C r : R⟦X⟧) ≃ₗ[R⟦X⟧] (H →ₗ[R⟦X⟧] E)) := fun ⟨e⟩ =>
  not_telescopeSurj_away hr0 hr ((telescopeSurj_dual H E X).of_linearEquiv e.symm)

end PowerSeries

section KXY

variable (k : Type u) [Field k]

/-- **Dimension two: `A_x` is not a Matlis dual.** For `A = k⟦x⟧⟦y⟧ = k[[x, y]]` and `f = x`,
`A_f` is not isomorphic, as an `A`-module, to `Hom_A(H, E)` for any module `H` and any injective
module `E` (in particular for `H = H²_x(j_!O_U)` and `E = E(k)`). -/
@[montpellier "101, 14–15"]
theorem not_nonempty_linearEquiv_dual (H E : Type v) [AddCommGroup H] [Module k⟦X⟧⟦X⟧ H]
    [AddCommGroup E] [Module k⟦X⟧⟦X⟧ E] [Module.Injective k⟦X⟧⟦X⟧ E] :
    ¬Nonempty (Localization.Away (C (X : k⟦X⟧) : k⟦X⟧⟦X⟧) ≃ₗ[k⟦X⟧⟦X⟧] (H →ₗ[k⟦X⟧⟦X⟧] E)) :=
  not_nonempty_linearEquiv_dual_powerSeries X_ne_zero
    (fun h => by simpa using h.map (constantCoeff (R := k))) H E

/-- **« φ n'est pas surjective ».** For `A = k[[x, y]]` and `f = x`, every injective `A`-linear
map `A_f → Hom_A(H, E)`, `E` injective, fails to be surjective. -/
@[montpellier "101, 14–15"]
theorem not_surjective_of_injective (H E : Type v) [AddCommGroup H] [Module k⟦X⟧⟦X⟧ H]
    [AddCommGroup E] [Module k⟦X⟧⟦X⟧ E] [Module.Injective k⟦X⟧⟦X⟧ E]
    (φ : Localization.Away (C (X : k⟦X⟧) : k⟦X⟧⟦X⟧) →ₗ[k⟦X⟧⟦X⟧] (H →ₗ[k⟦X⟧⟦X⟧] E))
    (hφ : Function.Injective φ) : ¬Function.Surjective φ := fun hs =>
  not_nonempty_linearEquiv_dual k H E ⟨LinearEquiv.ofBijective φ ⟨hφ, hs⟩⟩

end KXY

end Grothendieck.Folder101DimTwo
