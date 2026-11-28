/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Grothendieck.Attr

/-!
# Folder 9, pages 24 and 26: the determinant of a positive symmetric element, the algebraic core

Finding `9-symmetric-positive-det-sqrt-degree`. For `A` an ordinary polarised abelian variety and
`u ∈ End(A) ⊗ ℚ` symmetric and positive for the Rosati involution `*`, the determinant `Δ(u)` of
`u` on the étale part of `T_p(A)` is `+√(deg u)`. Page 24 gets `Δ(u)² = deg u` from
`Δ(u) Δ(u*) = deg u` and `u* = u`; page 26 settles the sign: `Δ` is a polynomial with rational
coefficients on the symmetric part, so extends to `End(A) ⊗ ℝ`, where every positive element is
the square `v²` of a symmetric `v`, whence `Δ(u) = Δ(v)² ≥ 0`.

**The statement on abelian varieties is not proved here.** Abelian varieties, the Rosati
involution, Tate modules and their étale parts, and the input identity `Δ(u) Δ(u*) = deg u` are
not formalised: the identity is a **hypothesis** of the theorems below. What this file proves is
the page's argument once that identity and a symmetric square root are given, and the existence
of the square root in the model case the page has in mind, real symmetric matrices.

## Main results

* `sq_eq_of_star_eq` (p. 24): for `Δ` with `Δ(u) Δ(u*) = d` and `u* = u`, `Δ(u)² = d`.
* `nonneg_and_sq_eq_of_eq_mul_self` (p. 26): in a monoid with involution, if `u = v v` with
  `v* = v`, `Δ` multiplicative with values in an ordered ring and `Δ(u) Δ(u*) = d`, then
  `0 ≤ Δ(u)` and `Δ(u)² = d`; `eq_sqrt_of_eq_mul_self`: with real values, `Δ(u) = √d`.
* `exists_star_eq_mul_self_eq` (p. 26, model case): a positive semidefinite real matrix is the
  square of a symmetric matrix (Mathlib's `CFC.sqrt`).
* `det_eq_sqrt_det_mul_det_transpose` (p. 26, model case): for `Δ = det` on real matrices, with
  the transpose as involution and `deg A = det A · det Aᵀ`, the conclusion `det A = √(deg A)` for
  a positive semidefinite `A`, by the two results above.

## Implementation notes

The involution is Mathlib's `StarMul` (`star (x y) = star y * star x`, involutive), the transpose
for real matrices. The degree enters only through the value `d` of `Δ(u) Δ(u*)`, so no degree
map is defined.

## Not formalised

* Abelian varieties, the Rosati involution, `T_p` and its étale part, `deg`, and the identity
  `Δ(u) Δ(u*) = deg u` (hypothesis).
* The passage from `End(A) ⊗ ℚ` to `End(A) ⊗ ℝ`: that `Δ` is a polynomial with rational
  coefficients on the symmetric part, that its extension stays multiplicative, and that the
  positive cone of `End(A) ⊗ ℝ` has symmetric square roots; it is left.

## References

* A. Grothendieck, folder 9, pp. 24, 26 (finding `9-symmetric-positive-det-sqrt-degree`)
-/

@[expose] public section

namespace Grothendieck.Folder9

section Abstract

variable {M K : Type*} [Monoid M] [StarMul M] [CommRing K]

/-- `9-symmetric-positive-det-sqrt-degree` (folder 9, p. 24): if `Δ(u) Δ(u*) = d` and `u* = u`,
then `Δ(u)² = d`. The identity `Δ(u) Δ(u*) = deg u` is a hypothesis. -/
@[montpellier "9, 24"]
theorem sq_eq_of_star_eq (Δ : M → K) {u : M} {d : K} (hd : Δ u * Δ (star u) = d)
    (hu : star u = u) : Δ u ^ 2 = d := by
  rwa [hu, ← sq] at hd

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- `9-symmetric-positive-det-sqrt-degree` (folder 9, p. 26): if `u = v v` with `v* = v`, `Δ` is
multiplicative and `Δ(u) Δ(u*) = d`, then `Δ(u) = Δ(v)² ≥ 0` and `Δ(u)² = d`: `Δ(u)` is the
non-negative square root of `d`. -/
@[montpellier "9, 26"]
theorem nonneg_and_sq_eq_of_eq_mul_self (Δ : M →* K) {u v : M} {d : K}
    (hd : Δ u * Δ (star u) = d) (hv : star v = v) (huv : u = v * v) :
    0 ≤ Δ u ∧ Δ u ^ 2 = d := by
  subst huv
  exact ⟨by simpa using mul_self_nonneg (Δ v), sq_eq_of_star_eq Δ hd (by rw [star_mul, hv])⟩

/-- `9-symmetric-positive-det-sqrt-degree` (folder 9, pp. 24, 26), with real values:
`Δ(u) = √d`. -/
@[montpellier "9, 24, 26"]
theorem eq_sqrt_of_eq_mul_self (Δ : M →* ℝ) {u v : M} {d : ℝ} (hd : Δ u * Δ (star u) = d)
    (hv : star v = v) (huv : u = v * v) : Δ u = √d := by
  obtain ⟨h₀, h₂⟩ := nonneg_and_sq_eq_of_eq_mul_self Δ hd hv huv
  rw [← h₂, Real.sqrt_sq h₀]

end Abstract

section Matrix

open Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n]

/-- `9-symmetric-positive-det-sqrt-degree` (folder 9, p. 26), the model case: a positive
semidefinite real matrix is the square of a symmetric matrix, its square root. -/
@[montpellier "9, 26"]
theorem exists_star_eq_mul_self_eq {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ∃ v : Matrix n n ℝ, star v = v ∧ v * v = A := by
  classical
  exact ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self A hA.nonneg⟩

/-- `9-symmetric-positive-det-sqrt-degree` (folder 9, pp. 24, 26), the model case: for
`Δ = det` on real matrices, with the transpose as involution, a positive semidefinite `A` has
`det A = √(det A · det Aᵀ)`, by the square root of `exists_star_eq_mul_self_eq` and the argument
of `eq_sqrt_of_eq_mul_self`. -/
@[montpellier "9, 24, 26"]
theorem det_eq_sqrt_det_mul_det_transpose [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det = √(A.det * Aᵀ.det) := by
  obtain ⟨v, hv, hvA⟩ := exists_star_eq_mul_self_eq hA
  exact eq_sqrt_of_eq_mul_self detMonoidHom (d := A.det * Aᵀ.det) (by simp [star_eq_conjTranspose])
    hv hvA.symm

end Matrix

end Grothendieck.Folder9
