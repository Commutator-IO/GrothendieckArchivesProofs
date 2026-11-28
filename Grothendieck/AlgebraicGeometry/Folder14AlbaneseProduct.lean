/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Tactic.Abel
import Grothendieck.Attr

/-!
# Folder 14, pages 23–29, 33: the product of two algebraically trivial classes, the Albanese core

Finding `14-albanese-equivalence-ring`. Among the claims of these pages: in the quotient ring
of correspondences, the product of two algebraically trivial classes is zero. Page 29, Th. 1.6,
proves it from the fact that the 0-cycle `((x) − (y)) × ((x′) − (y′))` on `T × T′` has zero
Albanese sum, the Albanese of `T × T′` being the product of the Albaneses of `T` and `T′`.

**Th. 1.6 is not proved here.** Cycles on varieties, correspondences and their composition, the
Albanese variety and the equivalence relations on cycles are not formalised; the identification
`Alb(T × T′) = Alb(T) × Alb(T′)` is a **hypothesis**, built into the definition of `albSum`
below. What is proved is the bilinear computation behind the page: 0-cycles are finitely
supported functions to `ℤ`, the Albanese sum on `T × T′` is
`Σ n_{(p, p′)} (a p, a′ p′) ∈ A × A′` for maps `a : T → A`, `a′ : T′ → A′` to abelian groups,
and the exterior product of two cycles of degree `0` has degree `0` and zero Albanese sum.

## Main definitions

* `deg`: the degree `Σ n_p` of a 0-cycle `z : X →₀ ℤ`.
* `albSum a`: the sum `Σ n_p a p` of a 0-cycle, for `a : X → A`.
* `extProd z z′`: the exterior product `Σ n_p n′_{p′} (p, p′)` on `X × X′`.

## Main results

* `deg_extProd`: `deg (z × z′) = deg z · deg z′`.
* `albSum_extProd`: `albSum (a × a′) (z × z′) = (deg z′ • albSum a z, deg z • albSum a′ z′)`,
  where `a × a′ : (p, p′) ↦ (a p, a′ p′)`.
* `albSum_extProd_eq_zero` (p. 29): the exterior product of two cycles of degree `0` has zero
  Albanese sum.
* `extProd_sub_single` (p. 29): `((x) − (y)) × ((x′) − (y′)) =
  (x, x′) − (x, y′) − (y, x′) + (y, y′)`.
* `deg_extProd_sub_single`, `albSum_extProd_sub_single` (p. 29): this cycle has degree `0` and
  zero Albanese sum.

## Implementation notes

The varieties `T`, `T′` are replaced by arbitrary types `X`, `X′`, their 0-cycles by `X →₀ ℤ`, and
the Albanese maps by arbitrary maps `a : X → A`, `a′ : X′ → A′`; the Albanese map of `X × X′` is
`(p, p′) ↦ (a p, a′ p′)`, which is where `Alb(T × T′) = Alb(T) × Alb(T′)` enters.

## Not formalised

* Varieties, cycles and correspondences on them, their composition and the quotient ring.
* The Albanese variety, the Albanese map, and `Alb(T × T′) = Alb(T) × Alb(T′)` (hypothesis).
* Th. 1.6 itself and the rest of pp. 23–29, 33.

## References

* A. Grothendieck, folder 14, pp. 23–29, 33 (finding `14-albanese-equivalence-ring`)
-/

@[expose] public section

namespace Grothendieck.Folder14

open Finsupp

variable {X X' A A' : Type*} [AddCommGroup A] [AddCommGroup A']

/-- The degree `Σ n_p` of a 0-cycle `z = Σ n_p (p)`. -/
noncomputable def deg : (X →₀ ℤ) →+ ℤ :=
  liftAddHom fun _ => AddMonoidHom.id ℤ

/-- The Albanese sum `Σ n_p a p` of a 0-cycle, for a map `a : X → A` to an abelian group. -/
noncomputable def albSum (a : X → A) : (X →₀ ℤ) →+ A :=
  liftAddHom fun p => zmultiplesHom A (a p)

/-- The exterior product `Σ n_p n′_{p′} (p, p′)` of two 0-cycles, biadditive: `(p) × z′` is the
image of `z′` under `p′ ↦ (p, p′)`. -/
noncomputable def extProd : (X →₀ ℤ) →+ (X' →₀ ℤ) →+ (X × X' →₀ ℤ) :=
  liftAddHom fun p => zmultiplesHom _ (mapDomain.addMonoidHom (Prod.mk p))

@[simp]
theorem deg_single (p : X) (n : ℤ) : deg (single p n) = n := by
  simp [deg]

@[simp]
theorem albSum_single (a : X → A) (p : X) (n : ℤ) : albSum a (single p n) = n • a p := by
  simp [albSum]

@[simp]
theorem extProd_single_single (p : X) (p' : X') (n n' : ℤ) :
    extProd (single p n) (single p' n') = single (p, p') (n * n') := by
  simp [extProd, mapDomain_single, smul_single]

/-- `deg (z × z′) = deg z · deg z′`. -/
@[montpellier "14, 29"]
theorem deg_extProd (z : X →₀ ℤ) (z' : X' →₀ ℤ) : deg (extProd z z') = deg z * deg z' := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂, add_mul]
  | single p n =>
    induction z' using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp_all [mul_add]
    | single p' n' => simp

/-- The Albanese sum of an exterior product, for the Albanese map `(p, p′) ↦ (a p, a′ p′)` of
`X × X′` to `A × A′`: `albSum (z × z′) = (deg z′ • albSum a z, deg z • albSum a′ z′)`. -/
@[montpellier "14, 29"]
theorem albSum_extProd (a : X → A) (a' : X' → A') (z : X →₀ ℤ) (z' : X' →₀ ℤ) :
    albSum (fun q => (a q.1, a' q.2)) (extProd z z') =
      (deg z' • albSum a z, deg z • albSum a' z') := by
  induction z using Finsupp.induction_linear with
  | zero => simp [Prod.zero_eq_mk]
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂, smul_add, add_smul]
  | single p n =>
    induction z' using Finsupp.induction_linear with
    | zero => simp [Prod.zero_eq_mk]
    | add z₁ z₂ h₁ h₂ => simp_all [smul_add, add_smul]
    | single p' n' => simp [mul_smul, smul_comm n' n]

/-- `14-albanese-equivalence-ring` (folder 14, p. 29): the exterior product of two 0-cycles of
degree `0` has zero Albanese sum on `X × X′`. -/
@[montpellier "14, 29"]
theorem albSum_extProd_eq_zero (a : X → A) (a' : X' → A') {z : X →₀ ℤ} {z' : X' →₀ ℤ}
    (hz : deg z = 0) (hz' : deg z' = 0) : albSum (fun q => (a q.1, a' q.2)) (extProd z z') = 0 := by
  simp [albSum_extProd, hz, hz']

/-- `14-albanese-equivalence-ring` (folder 14, p. 29): `((x) − (y)) × ((x′) − (y′)) =
(x, x′) − (x, y′) − (y, x′) + (y, y′)`. -/
@[montpellier "14, 29"]
theorem extProd_sub_single (x y : X) (x' y' : X') :
    extProd (single x 1 - single y 1) (single x' 1 - single y' 1) =
      single (x, x') 1 - single (x, y') 1 - single (y, x') 1 + single (y, y') 1 := by
  simp only [map_sub, AddMonoidHom.sub_apply, extProd_single_single, mul_one]
  abel

/-- `14-albanese-equivalence-ring` (folder 14, p. 29): the cycle
`((x) − (y)) × ((x′) − (y′))` has degree `0`. -/
@[montpellier "14, 29"]
theorem deg_extProd_sub_single (x y : X) (x' y' : X') :
    deg (extProd (single x 1 - single y 1) (single x' 1 - single y' 1)) = 0 := by
  simp

/-- `14-albanese-equivalence-ring` (folder 14, p. 29): the cycle
`((x) − (y)) × ((x′) − (y′))` has zero Albanese sum on `X × X′`. -/
@[montpellier "14, 29"]
theorem albSum_extProd_sub_single (a : X → A) (a' : X' → A') (x y : X) (x' y' : X') :
    albSum (fun q => (a q.1, a' q.2))
      (extProd (single x 1 - single y 1) (single x' 1 - single y' 1)) = 0 :=
  albSum_extProd_eq_zero a a' (by simp) (by simp)

end Grothendieck.Folder14
