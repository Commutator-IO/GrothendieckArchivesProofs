/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DividedPowerPolynomialAlgebra

/-!
# Folder 136, pages 5 to 7: the differential of a divided power, Stacks version

The setting is the divided power de Rham complex of the Stacks project.

`Grothendieck/Folder136.lean` works in a coordinate model: a form on the `m`-simplex is the
function `f a β I` of its coefficients on `T^{(a)} Y^{(β)} dY_I`, and its differential `pdD`
is defined by the rule of pages 5 to 7, `d(Y^{(n+1)}) = Y^{(n)} dY`. The identification of this
model with an intrinsic divided power de Rham complex was left out there.

## Main results

Let `(B, I, δ)` be a divided power ring over `A` and `P = B⟨Y_w⟩`, with its divided powers on
`IP + P₊` (Stacks tag 07H6).

* `dividedPowerDifferential_variableMonomial`: `d(Y_w^{[n+1]}) = Y_w^{[n]} · dY_w` in
  `Ω¹_{P/A,δ}`, the rule of page 5, here a theorem about the universal divided power
  differential rather than a definition;
* `dividedPowerDifferentialsEquiv_variableMonomial`: in the coordinates of 07HS,
  `d(Y_w^{[n+1]})` has no component along `Ω¹_B` and the single coordinate `Y_w^{[n]}` along
  `dY_w`. This is the degree `0 → 1` part of `pdD` in `Folder136.lean`: the coefficient of
  `dY_w` in `d(Y_w^{(n+1)})` is `Y_w^{(n)}`, which is what `pdD f (a, β, {w}) = f (a, β + e_w, ∅)`
  says on a one-variable monomial.

## Implementation notes

The vendored AxiomMath/Stacks files supply the intrinsic side: the module `Ω¹_{P/A,δ}` of divided
power differentials of a divided power ring (Stacks tag 07HZ, file
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/DeRham.lean`), and, for the divided
power polynomial algebra `P = B⟨Y_w : w ∈ W⟩`, its decomposition
`Ω¹_{P/A,δ} ≅ (P ⊗_B Ω¹_{B/A,δ}) ⊕ ⨁_w P · dY_w` (tag 07HS, file
`…/Differentials/DividedPowerPolynomialAlgebra.lean`).

## Not formalised

The same identification in every exterior degree and for products of monomials (the full
isomorphism of the coordinate complex with `Crystalline.dividedPowerDeRhamComplex`).
Proposition 1 (`Φ_* ≃ 0`) is in `Grothendieck/Folder136Prop1.lean`.

## References

* A. Grothendieck, cote 136, pp. 5–7
* Stacks Project, tags 07HZ, 07HS, 07H6
-/

@[expose] public section


namespace Grothendieck.Folder136

open Crystalline DividedPowers

universe uA uB uW

variable {A : Type uA} [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- `d(Y_w^{[n+1]}) = Y_w^{[n]} · dY_w` for the universal divided power differential of the
divided power polynomial algebra `B⟨Y_w : w ∈ W⟩` (page 5). -/
theorem dividedPowerDifferential_variableMonomial (w : W) (n : ℕ) :
    dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
        (dividedPowerPolynomialVariableMonomial (B : Type uB) w (n + 1)) =
      dividedPowerPolynomialVariableMonomial (B : Type uB) w n •
        dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
          (dividedPowerPolynomialVariable (B : Type uB) w) := by
  have h := dividedPowerDifferential_dpow (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W)
    ⟨dividedPowerPolynomialVariable (B : Type uB) w, variable_mem_polynomialIdeal B w⟩ n
  simpa only [setIndexedDividedPowerPolynomialDividedPowers_dpow_variable] using h

/-- In the coordinates `Ω¹_{P/A,δ} ≅ (P ⊗_B Ω¹_{B/A,δ}) ⊕ ⨁_w P · dY_w` of Stacks tag 07HS,
`d(Y_w^{[n+1]})` is `Y_w^{[n]}` times the basis vector `dY_w`, as in the coordinate model of
`Folder136.lean`. -/
theorem dividedPowerDifferentialsEquiv_variableMonomial (w : W) (n : ℕ) :
    (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1
        (dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
          (dividedPowerPolynomialVariableMonomial (B : Type uB) w (n + 1))) =
      (0, Finsupp.single w (dividedPowerPolynomialVariableMonomial (B : Type uB) w n)) := by
  rw [dividedPowerDifferential_variableMonomial, LinearEquiv.map_smul,
    (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).2.2 w,
    Prod.smul_mk, smul_zero, Finsupp.smul_single, smul_eq_mul, mul_one]

end Grothendieck.Folder136
