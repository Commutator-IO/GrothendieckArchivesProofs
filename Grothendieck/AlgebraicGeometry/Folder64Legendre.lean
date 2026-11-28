/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.GroupTheory.Perm.Fin
import Grothendieck.Attr

/-!
# Folder 64, pages 74–79 and 84–91: the Legendre family and the action of `𝔖₃` through the sign

The modernised reading `transcripts/64/64.modern.tex` (part III, « L'épinglage de Legendre sur un
corps », « … sur une base ; le schéma de modules ») states that, over `ℤ[1/2]`, elliptic curves
with a Jacobi pinning of level 2 (an ordering of the 2-torsion, which identifies `Σ = E/±1` with
`ℙ¹`, the three points of order 2 going to `0, 1, ∞` and the origin to a point `t` of `U_{0,3}`)
and a Legendre pinning (a tangent vector at the origin, twisted by a fixed `μ₄`-torsor, whose
square matches `T_{Σ,t}`) form a rigid groupoid represented by `U_{0,3} × μ₄*`: the Legendre
family `λ = t`. By (47), (51)–(53) of pages 88–91, `μ₄ × 𝔖₃` acts on it, `𝔖₃` tautologically on
`U_{0,3}` and through the sign on `μ₄*`, and the tangent bundle carries the twist `λ² sg(g)` of
the tautological action of `O(2)`. This file proves the algebra behind that action, for the
Weierstrass models of Mathlib, and nothing about the groupoid. It is the reachable part of finding
`64-legendre-pinning-moduli` of `src/content/findings.ts`.

## Main results

Let `e = (0, 1, t)` be the roots of the Legendre curve `E_t : y² = x(x − 1)(x − t)`. A permutation
`σ` of the three roots gives the new parameter `t'` with `(e σ1 − e σ0) t' = e σ2 − e σ0`, the
image of `t` by the Möbius map `g_σ = (A t + B)/(C t + D)` of the six substitutions
`t ↦ t, 1 − t, 1/t, t/(t − 1), 1/(1 − t), (t − 1)/t`; its automorphy factor
`C t + D = e σ1 − e σ0` is `scale t σ`.

* `legendre_Δ`, `legendre_c₄`, `isElliptic_legendre`, `legendre_j`: `Δ(E_t) = 16 t² (t − 1)²`,
  a unit when `2`, `t`, `t − 1` are, and `j(E_t) t² (t − 1)² = 256 (t² − t + 1)³`.
* `legendre_variableChange`: the change of variables `x = u² x' + e σ0`, `y = u³ y'` takes `E_t`
  to `E_{t'}` as soon as `u² = C t + D`. For `t ↦ 1 − t` this is `u² = −1`
  (`legendre_one_sub`: `u = i`), for `t ↦ 1/t` it is `u² = t`: on `E_t` itself the action of
  `𝔖₃` needs square roots of `−1`, `t` and `1 − t`, and the scaling `u` of the tangent vector is
  not a root of unity.
* `legendre_j_perm`: hence `j(E_{t'}) = j(E_t)`.
* `det_mobius`: `A D − B C = sg(σ)`, so the derivative `g_σ'(t) = sg(σ)/(C t + D)²` is the
  tautological action on `O(2)` twisted by the sign, as in (53).
* `pinned_variableChange`, `pinned_tangent`, `pinned_tangent_sq`: on the model
  `Y² = X(X − F)(X − F t)`, `F = t (t − 1)`, with the tangent vector `v_t = F⁻¹ ∂_W` at the origin
  (`W = X/Y`), the six substitutions are the changes of variables with `u = ζ (C t + D)²` and
  `ζ² = sg(σ)`, and they carry `v_t` to `s v_{t'}` with `s (C t + D) = sg(σ) ζ`: the scaling
  `s` is the automorphy factor of `O(1)` times a fourth root of unity whose square is the sign,
  and `s² (C t + D)² = A D − B C`, i.e. `s² = g_σ'(t)`. An even `σ` needs only `ζ = ±1`; an odd
  one needs `ζ = ±i`, a point of `μ₄*`. This is the coordinate form of « `𝔖₃` acts on `μ₄*`
  through the sign », (47), and of (51 bis), `T_g ζ = χ₄(g) (g · ζ)` with `χ₄(g)² = sg(g)`: the
  identification of a Legendre pinning with a point of `μ₄*` is not modelled, so the action on
  the scheme `U_{0,3} × μ₄*` itself is not derived.

## Implementation notes

The normalisation of the Legendre pinning is ours. Its page-free content is this: with
`z = t (x − 1)/(x − t)`, the coordinate on `Σ` in which the 2-torsion `x = 0, 1, t` is at
`1, 0, ∞` and the origin at `t`, one has `z − t ∼ F² W²` near the origin of the model above, so
`v_t² = ∂_z` in `T_{Σ,t}`; this replaces the page's `O(1)^♮`, and the twist by the `μ₄`-torsor
`Q₀` (the roots of `x⁴ = −4` in the reading) becomes the choice of `ζ`. The model is the quadratic
twist `F y² = x(x − 1)(x − t)` of the Legendre curve (`X = F x`, `Y = F² y`): it is the twist
that makes the six isomorphisms defined over `ℤ[i][t, 1/F]`. The tangent space at the origin
is not in Mathlib: that the change `(u, r, 0, 0)` multiplies `∂_W` by `u` is read off `W = X/Y`
and is not proved. The identities are proved over any commutative ring, the new parameter `t'`
being given by the relation `(C t + D) t' = A t + B`, so that no inverse is taken. The six
permutations are enumerated by `decide` (`perm_fin_three`).

## Not formalised

The groupoids of Legendre and Legendre–Jacobi pinnings, their rigidity, their representability by
`U_{0,3} × μ₄*`, the torsors `Q₀`, `L_{E/S}` and the action of `μ₄ × 𝔖₃` on the scheme
`U_{0,3} × μ₄*` and on `O(1)`; the subgroup `𝔻'₃` and its character `χ₄`; the statements over a
base. Mathlib has no moduli stacks; only the coordinate identities above are proved.

## References

* A. Grothendieck, folder 64, pp. 74–79, 84–91, formulas (47)–(53) (finding
  `64-legendre-pinning-moduli`); modernised reading `transcripts/64/64.modern.tex`, part III
-/

@[expose] public section


namespace Grothendieck.Folder64Legendre

open Equiv WeierstrassCurve WeierstrassCurve.VariableChange

/-- The six permutations of `Fin 3`. -/
theorem perm_fin_three (σ : Perm (Fin 3)) :
    σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 0 2 ∨ σ = swap 1 2 ∨ σ = swap 0 1 * swap 0 2 ∨
      σ = swap 0 2 * swap 0 1 := by
  revert σ; decide

variable {R : Type*} [CommRing R]

/-- The Weierstrass curve `y² = (x − e₀)(x − e₁)(x − e₂)`. -/
def rootsCurve (e : Fin 3 → R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := -(e 0 + e 1 + e 2)
  a₃ := 0
  a₄ := e 0 * e 1 + e 0 * e 2 + e 1 * e 2
  a₆ := -(e 0 * e 1 * e 2)

/-- The curve does not depend on the order of the roots. -/
lemma rootsCurve_comp (e : Fin 3 → R) (σ : Perm (Fin 3)) : rootsCurve (e ∘ σ) = rootsCurve e := by
  rcases perm_fin_three σ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    ext <;> simp [rootsCurve, swap_apply_def] <;> ring

/-- The change of variables `x = u² x' + r`, `y = u³ y'` moves the roots `e` to `e'` when
`e = u² e' + r`. -/
lemma variableChange_rootsCurve (u : Rˣ) (r : R) (e e' : Fin 3 → R)
    (h : ∀ i, e i = u ^ 2 * e' i + r) :
    (⟨u, r, 0, 0⟩ : VariableChange R) • rootsCurve e = rootsCurve e' := by
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, rootsCurve, h] <;> ring_nf <;> simp [← mul_pow]

/-- The Vandermonde product of three roots changes by the sign of a permutation. -/
lemma vandermonde_comp (e : Fin 3 → R) (σ : Perm (Fin 3)) :
    (e (σ 1) - e (σ 0)) * (e (σ 2) - e (σ 0)) * (e (σ 2) - e (σ 1)) =
      (Perm.sign σ : ℤ) * ((e 1 - e 0) * (e 2 - e 0) * (e 2 - e 1)) := by
  rcases perm_fin_three σ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Perm.mul_apply, swap_apply_def, Perm.sign_mul, Perm.sign_swap'] <;> ring

lemma sign_sq (σ : Perm (Fin 3)) : ((Perm.sign σ : ℤ) : R) ^ 2 = 1 := by
  simp [← Int.cast_pow, ← Units.val_pow_eq_pow_val]

/-! ### The Legendre curve -/

/-- The Legendre curve `E_t : y² = x(x − 1)(x − t)`. -/
def legendre (t : R) : WeierstrassCurve R := rootsCurve ![0, 1, t]

@[montpellier "64, 74–79"]
theorem legendre_Δ (t : R) : (legendre t).Δ = 16 * t ^ 2 * (t - 1) ^ 2 := by
  simp [legendre, rootsCurve, Δ, b₂, b₄, b₆, b₈]
  ring

theorem legendre_c₄ (t : R) : (legendre t).c₄ = 16 * (t ^ 2 - t + 1) := by
  simp [legendre, rootsCurve, c₄, b₂, b₄]
  ring

/-- Over a ring where `2`, `t` and `t − 1` are units, `E_t` is an elliptic curve. -/
@[montpellier "64, 74–79"]
theorem isElliptic_legendre {t : R} (h2 : IsUnit (2 : R)) (ht : IsUnit t) (ht1 : IsUnit (t - 1)) :
    (legendre t).IsElliptic :=
  ⟨by rw [legendre_Δ, show (16 : R) = 2 ^ 4 by norm_num]
      exact ((h2.pow 4).mul (ht.pow 2)).mul (ht1.pow 2)⟩

/-- `j(E_t) = 256 (t² − t + 1)³ / (t² (t − 1)²)`. -/
@[montpellier "64, 74–79"]
theorem legendre_j (t : R) [(legendre t).IsElliptic] :
    (legendre t).j * (t ^ 2 * (t - 1) ^ 2) = 256 * (t ^ 2 - t + 1) ^ 3 := by
  have h1 : (legendre t).j * (legendre t).Δ = (legendre t).c₄ ^ 3 := by
    rw [j, ← coe_Δ', mul_right_comm, Units.inv_mul, one_mul]
  rw [legendre_Δ, legendre_c₄] at h1
  have h16 := legendre_Δ t ▸ (legendre t).isUnit_Δ
  exact (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h16)).mul_left_cancel
    (by linear_combination h1)

/-! ### The six substitutions -/

/-- The automorphy factor `C t + D = e σ1 − e σ0` of the substitution `σ`. -/
def scale (t : R) (σ : Perm (Fin 3)) : R := ![0, 1, t] (σ 1) - ![0, 1, t] (σ 0)

/-- The numerator `A t + B = e σ2 − e σ0`: the new parameter is `(A t + B)/(C t + D)`. -/
def numer (t : R) (σ : Perm (Fin 3)) : R := ![0, 1, t] (σ 2) - ![0, 1, t] (σ 0)

/-- Pages 84–91: the substitution `σ` of the roots is the change of variables
`x = u² x' + e σ0`, `y = u³ y'` from `E_t` to `E_{t'}`, `t' = (A t + B)/(C t + D)`, for any `u`
with `u² = C t + D`. -/
@[montpellier "64, 84–91"]
theorem legendre_variableChange (σ : Perm (Fin 3)) {t t' : R} (u : Rˣ)
    (hu : (u : R) ^ 2 = scale t σ) (ht' : t' * scale t σ = numer t σ) :
    (⟨u, ![0, 1, t] (σ 0), 0, 0⟩ : VariableChange R) • legendre t = legendre t' := by
  rw [legendre, ← rootsCurve_comp _ σ]
  refine variableChange_rootsCurve _ _ _ _ fun i => ?_
  simp only [scale, numer] at hu ht'
  fin_cases i <;> simp [hu]
  linear_combination -ht'

/-- `t ↦ 1 − t`, the transposition of the roots `0` and `1`, needs `u = i` with `i² = −1`. -/
@[montpellier "64, 84–91"]
theorem legendre_one_sub (t : R) (i : Rˣ) (hi : (i : R) ^ 2 = -1) :
    (⟨i, 1, 0, 0⟩ : VariableChange R) • legendre t = legendre (1 - t) := by
  simpa using legendre_variableChange (t' := 1 - t) (swap 0 1) i (by simp [scale, hi])
    (by simp [scale, numer, swap_apply_of_ne_of_ne])

/-- The six substitutions preserve `j`. -/
@[montpellier "64, 84–91"]
theorem legendre_j_perm (σ : Perm (Fin 3)) {t t' : R} (u : Rˣ) (hu : (u : R) ^ 2 = scale t σ)
    (ht' : t' * scale t σ = numer t σ) [(legendre t).IsElliptic] [(legendre t').IsElliptic] :
    (legendre t').j = (legendre t).j := by
  rw [← variableChange_j (W := legendre t) (C := ⟨u, ![0, 1, t] (σ 0), 0, 0⟩)]
  simp_rw [legendre_variableChange σ u hu ht']

/-! ### The Möbius map of a substitution -/

/-- The coefficients of `t` in the roots `0, 1, t`. -/
def p : Fin 3 → ℤ := ![0, 0, 1]

/-- The constant terms of the roots `0, 1, t`. -/
def q : Fin 3 → ℤ := ![0, 1, 0]

/-- The matrix `(A B; C D)` of the Möbius map `t ↦ (A t + B)/(C t + D)` of `σ`. -/
def mobius (σ : Perm (Fin 3)) : ℤ × ℤ × ℤ × ℤ :=
  (p (σ 2) - p (σ 0), q (σ 2) - q (σ 0), p (σ 1) - p (σ 0), q (σ 1) - q (σ 0))

lemma scale_eq (t : R) (σ : Perm (Fin 3)) :
    scale t σ = (mobius σ).2.2.1 * t + (mobius σ).2.2.2 ∧
      numer t σ = (mobius σ).1 * t + (mobius σ).2.1 := by
  have he (i : Fin 3) : ![0, 1, t] i = p i * t + q i := by fin_cases i <;> simp [p, q]
  simp only [scale, numer, mobius, he]
  push_cast
  constructor <;> ring

/-- The determinant of the Möbius map of `σ` is the sign of `σ`: its derivative at `t` is
`sg(σ)/(C t + D)²`, the action on `O(2)` twisted by the sign, (53). -/
@[montpellier "64, 84–91"]
theorem det_mobius (σ : Perm (Fin 3)) :
    (mobius σ).1 * (mobius σ).2.2.2 - (mobius σ).2.1 * (mobius σ).2.2.1 = Perm.sign σ := by
  revert σ; decide

/-! ### The pinned model -/

/-- `F(t) = t (t − 1)`. -/
def F (t : R) : R := t * (t - 1)

/-- The model `Y² = X(X − F)(X − F t)` of the twist `F y² = x(x − 1)(x − t)` of `E_t`, on which
the pinned tangent vector is `F⁻¹ ∂_W`. -/
def pinned (t : R) : WeierstrassCurve R := rootsCurve fun i => F t * ![0, 1, t] i

/-- The cocycle of `F`: `(C t + D)³ F(t') = sg(σ) F(t)`. -/
lemma scale_pow_three_mul_F (σ : Perm (Fin 3)) {t t' : R} (ht' : t' * scale t σ = numer t σ) :
    scale t σ ^ 3 * F t' = (Perm.sign σ : ℤ) * F t := by
  have hv := vandermonde_comp ![0, 1, t] σ
  simp only [scale, numer, F] at ht' ⊢
  simp only [Matrix.cons_val] at hv
  linear_combination ((![0, 1, t] (σ 1) - ![0, 1, t] (σ 0)) *
      ((![0, 1, t] (σ 1) - ![0, 1, t] (σ 0)) * t' + (![0, 1, t] (σ 2) - ![0, 1, t] (σ 0))) -
      (![0, 1, t] (σ 1) - ![0, 1, t] (σ 0)) ^ 2) * ht' + hv

/-- Pages 84–91: on the pinned model, the substitution `σ` is the change of variables
`X = u² X' + F e σ0`, `Y = u³ Y'` with `u = ζ (C t + D)²`, for any `ζ` with `ζ² = sg(σ)`. -/
@[montpellier "64, 84–91"]
theorem pinned_variableChange (σ : Perm (Fin 3)) {t t' ζ : R} (u : Rˣ)
    (hζ : ζ ^ 2 = (Perm.sign σ : ℤ)) (hu : (u : R) = ζ * scale t σ ^ 2)
    (ht' : t' * scale t σ = numer t σ) :
    (⟨u, F t * ![0, 1, t] (σ 0), 0, 0⟩ : VariableChange R) • pinned t = pinned t' := by
  have hc := scale_pow_three_mul_F σ ht'
  have hs := sign_sq (R := R) σ
  rw [pinned, ← rootsCurve_comp _ σ]
  refine variableChange_rootsCurve _ _ _ _ fun i => ?_
  have key : F t * scale t σ = u ^ 2 * F t' := by
    linear_combination (-((u : R) + ζ * scale t σ ^ 2) * F t') * hu - scale t σ ^ 4 * F t' * hζ -
      ((Perm.sign σ : ℤ) : R) * scale t σ * hc - scale t σ * F t * hs
  simp only [scale, numer] at key ht'
  fin_cases i <;> simp
  · linear_combination key
  · linear_combination t' * key - F t * ht'

/-- The tangent vector: the change of `pinned_variableChange` multiplies `∂_W` by `u`, so
`v_t = F(t)⁻¹ ∂_W` by `s = u F(t')/F(t)`, and `s (C t + D) = sg(σ) ζ`, a fourth root of unity
whose square is `sg(σ)`. -/
@[montpellier "64, 84–91"]
theorem pinned_tangent (σ : Perm (Fin 3)) {t t' ζ : R} (u : Rˣ)
    (hζ : ζ ^ 2 = (Perm.sign σ : ℤ)) (hu : (u : R) = ζ * scale t σ ^ 2)
    (ht' : t' * scale t σ = numer t σ) :
    u * F t' * scale t σ = (Perm.sign σ : ℤ) * ζ * F t ∧
      (((Perm.sign σ : ℤ) : R) * ζ) ^ 2 = (Perm.sign σ : ℤ) := by
  refine ⟨?_, by rw [mul_pow, sign_sq, hζ, one_mul]⟩
  linear_combination (F t' * scale t σ) * hu + ζ * scale_pow_three_mul_F σ ht'

/-- The pinning is respected: `s² (C t + D)² = A D − B C`, that is `s² = g_σ'(t)`, the
derivative at `t` of the Möbius map of `σ` (`det_mobius`). -/
@[montpellier "64, 84–91"]
theorem pinned_tangent_sq (σ : Perm (Fin 3)) {t t' ζ : R} (u : Rˣ)
    (hζ : ζ ^ 2 = (Perm.sign σ : ℤ)) (hu : (u : R) = ζ * scale t σ ^ 2)
    (ht' : t' * scale t σ = numer t σ) :
    (u * F t') ^ 2 * ((mobius σ).2.2.1 * t + (mobius σ).2.2.2) ^ 2 =
      (((mobius σ).1 * (mobius σ).2.2.2 - (mobius σ).2.1 * (mobius σ).2.2.1 : ℤ) : R) *
        F t ^ 2 := by
  obtain ⟨h1, h2⟩ := pinned_tangent σ u hζ hu ht'
  rw [← (scale_eq t σ).1, det_mobius, ← h2]
  linear_combination (u * F t' * scale t σ + (Perm.sign σ : ℤ) * ζ * F t) * h1

end Grothendieck.Folder64Legendre
