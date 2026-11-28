/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Rat.Init
import Grothendieck.Attr

/-!
# Folder 147, pages 62–64: the stratified class of `M₁,₁` over `ℤ`

The page computes the class of the moduli stack of elliptic curves over all of `ℤ` by cutting the
`j`-line `𝔸¹_ℤ` along the two sections `S₀` (`j = 1728`, automorphisms `ℤ/4`) and `S₁` (`j = 0`,
automorphisms `ℤ/6`), which meet only over `𝔽₂` and `𝔽₃`, where the automorphism groups have order
24 and 12. With `𝕃` the class of the affine line and `ζ_p` the class of `Spec 𝔽_p`, the strata give

  `[M₁,₁] = ½[U] + ¼[S'₀] + ⅙[S'₁] + (1/24) ζ₂ + (1/12) ζ₃`,
  `[U] = 𝕃 − 2 + ζ₂ + ζ₃`, `[S'ᵢ] = 1 − ζ₂ − ζ₃`,

and the page's formula (80) is `[M₁,₁] = ½(𝕃 − 1) − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`; adding the cusp, with
weight ½, gives `[M̄₁,₁] = ½ 𝕃 − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`. The modernised reading says it redid the
computation (« il est juste »); this file checks the arithmetic, over any field of characteristic
zero, with `𝕃`, `ζ₂`, `ζ₃` as indeterminates.

## Main results

The first three statements are the arithmetic alone, in a field `K` of characteristic zero.

* `class_M11`, `class_M11_bar`, `class_M11_away_from_6`: formula (80), the compactified class and
  the case `ζ₂ = ζ₃ = 0`, the classes of the strata being substituted by hand.

The others derive the classes of the strata instead of assuming them. The five pieces `U`, `S'₀`,
`S'₁`, `a₂`, `a₃` are the atoms of the Boolean algebra that the two sections and the two points
generate on the `j`-line, and an additive function on it, with values in a `K`-vector space `M`
(a `ℚ`-vector space for `K = ℚ`), is the choice of five elements `u`, `s₀`, `s₁`, `z₂`, `z₃` of
`M`, the class of a union of atoms being the sum. The hypotheses are then the three relations the
page reads off the geometry: the whole line has class `L`, and each section, a copy of `Spec ℤ`
made of its primed part and of the two points, has class `one`.

* `class_strata`: `[U] = L − 2 + ζ₂ + ζ₃` and `[S'₀] = [S'₁] = 1 − ζ₂ − ζ₃`;
* `class_M11_of_strata`: the sum of the atoms weighted by `½`, `¼`, `⅙`, `1/24`, `1/12` is
  `½(L − 1) − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`, formula (80);
* `class_M11_bar_of_strata`: with the cusp, `½ L − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`;
* `class_M11_of_strata_away_from_6`: without the two points, `½(L − 1) − 1/12` and
  `½(L − 1) + 5/12`;
* `pointCount_M11`: for `L ↦ p`, `1 ↦ 1` the value is `½(p − 1) − 1/12`, which is not `p`.

The page's value comes out of these relations as it stands: there is no discrepancy with (80).

## Not formalised

It checks the algebra of the strata, not the geometry that produces them. The invariant itself is
not defined: neither its existence, nor its additivity, nor the classes of the `j`-line, of the
two sections and of their intersection, nor the orders 2, 4, 6, 24, 12 of the automorphism groups
are proved; they enter as the hypotheses and as the weights of the statements. Nothing is said of
the stack of elliptic curves.

## References

* A. Grothendieck, folder 147, pp. 62–64, formula (80)
-/

@[expose] public section


namespace Grothendieck.Folder147

variable {K : Type*} [Field K] [CharZero K]

/-- Formula (80) of folder 147, page 63, from the stratification of the `j`-line. -/
@[montpellier "147, 63"]
theorem class_M11 (L z₂ z₃ : K) :
    (1 / 2) * (L - 2 + z₂ + z₃) + (1 / 4) * (1 - z₂ - z₃) + (1 / 6) * (1 - z₂ - z₃)
        + (1 / 24) * z₂ + (1 / 12) * z₃
      = (1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃ := by
  ring

/-- The compactified class: the cusp adds `½`. -/
@[montpellier "147, 62–64"]
theorem class_M11_bar (L z₂ z₃ : K) :
    ((1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃) + 1 / 2
      = (1 / 2) * L - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃ := by
  ring

/-- Over `ℤ[1/6]` the correction terms vanish and (80) becomes (79). -/
@[montpellier "147, 62–64"]
theorem class_M11_away_from_6 (L : K) :
    (1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * 0 + (1 / 6) * 0 = (1 / 2) * (L - 1) - 1 / 12 := by
  ring

section Strata

variable {M : Type*} [AddCommGroup M]

/-- The classes of the strata of folder 147, page 63, for an additive function given by its values
`u`, `s₀`, `s₁`, `z₂`, `z₃` on the five pieces `U`, `S'₀`, `S'₁`, `a₂`, `a₃` of the `j`-line: if
the line has class `L` and each of the two sections `S₀ = S'₀ ∪ {a₂, a₃}`,
`S₁ = S'₁ ∪ {a₂, a₃}` has class `one`, then `[U] = L − 2 + ζ₂ + ζ₃` and
`[S'₀] = [S'₁] = 1 − ζ₂ − ζ₃`. That such a function exists on the pieces of a scheme is not
proved. -/
@[montpellier "147, 63"]
theorem class_strata {u s₀ s₁ z₂ z₃ one L : M} (hline : u + s₀ + s₁ + z₂ + z₃ = L)
    (hS₀ : s₀ + z₂ + z₃ = one) (hS₁ : s₁ + z₂ + z₃ = one) :
    u = L - one - one + z₂ + z₃ ∧ s₀ = one - z₂ - z₃ ∧ s₁ = one - z₂ - z₃ := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := abel) hline - hS₀ - hS₁
  · linear_combination (norm := abel) hS₀
  · linear_combination (norm := abel) hS₁

end Strata

variable {M : Type*} [AddCommGroup M] [Module K M]

/-- Formula (80) of folder 147, page 63, from the relations between the pieces of the `j`-line
rather than from the classes of the strata (`class_strata`): the pieces `U`, `S'₀`, `S'₁`, `a₂`,
`a₃`, counted with the inverses `½`, `¼`, `⅙`, `1/24`, `1/12` of the orders of their automorphism
groups, add up to `½(L − 1) − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`. The weights are those of the page; that they
are the orders of the automorphism groups of elliptic curves is not proved. -/
@[montpellier "147, 63"]
theorem class_M11_of_strata {u s₀ s₁ z₂ z₃ one L : M} (hline : u + s₀ + s₁ + z₂ + z₃ = L)
    (hS₀ : s₀ + z₂ + z₃ = one) (hS₁ : s₁ + z₂ + z₃ = one) :
    (1 / 2 : K) • u + (1 / 4 : K) • s₀ + (1 / 6 : K) • s₁ + (1 / 24 : K) • z₂ + (1 / 12 : K) • z₃
      = (1 / 2 : K) • (L - one) - (1 / 12 : K) • one + (1 / 8 : K) • z₂ + (1 / 6 : K) • z₃ := by
  obtain ⟨rfl, rfl, rfl⟩ := class_strata hline hS₀ hS₁
  module

/-- The compactified class, from the same relations: the cusp, a copy of `Spec ℤ` with
automorphism group of order 2, adds `½`, and the sum is `½ L − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`. -/
@[montpellier "147, 62–64"]
theorem class_M11_bar_of_strata {u s₀ s₁ z₂ z₃ one L : M}
    (hline : u + s₀ + s₁ + z₂ + z₃ = L) (hS₀ : s₀ + z₂ + z₃ = one) (hS₁ : s₁ + z₂ + z₃ = one) :
    (1 / 2 : K) • u + (1 / 4 : K) • s₀ + (1 / 6 : K) • s₁ + (1 / 24 : K) • z₂ + (1 / 12 : K) • z₃
        + (1 / 2 : K) • one
      = (1 / 2 : K) • L - (1 / 12 : K) • one + (1 / 8 : K) • z₂ + (1 / 6 : K) • z₃ := by
  obtain ⟨rfl, rfl, rfl⟩ := class_strata hline hS₀ hS₁
  module

/-- Over `ℤ[1/6]` the two sections are disjoint and the points `a₂`, `a₃` are gone: the line is
`U ∪ S₀ ∪ S₁`, and the two sums are `½(L − 1) − 1/12`, formula (79), and, with the cusp,
`½(L − 1) + 5/12`. -/
@[montpellier "147, 62–64"]
theorem class_M11_of_strata_away_from_6 {u s₀ s₁ one L : M} (hline : u + s₀ + s₁ = L)
    (hS₀ : s₀ = one) (hS₁ : s₁ = one) :
    (1 / 2 : K) • u + (1 / 4 : K) • s₀ + (1 / 6 : K) • s₁
        = (1 / 2 : K) • (L - one) - (1 / 12 : K) • one ∧
      (1 / 2 : K) • u + (1 / 4 : K) • s₀ + (1 / 6 : K) • s₁ + (1 / 2 : K) • one
        = (1 / 2 : K) • (L - one) + (5 / 12 : K) • one := by
  subst hline hS₀ hS₁
  constructor <;> module

/-- A check on formula (79): over `𝔽_p`, `p ≥ 5`, the pieces `U`, `S₀`, `S₁` of the `j`-line have
`p − 2`, `1` and `1` rational points, and the weighted sum is `½(p − 1) − 1/12`, the value of (79)
at `L ↦ p`, `1 ↦ 1`. It is never `p`, the number of elliptic curves over `𝔽_p` counted with the
inverses of the orders of their automorphism groups: the invariant counts the points of the coarse
space, not the curves (that number, `p`, is not proved here). -/
@[montpellier "147, 62–64"]
theorem pointCount_M11 (p : ℕ) :
    (1 / 2 : K) * (p - 2) + 1 / 4 + 1 / 6 = (1 / 2) * (p - 1) - 1 / 12 ∧
      (1 / 2 : K) * (p - 1) - 1 / 12 ≠ p := by
  refine ⟨by ring, fun h => ?_⟩
  have h' : ((6 * p + 7 : ℕ) : K) = 0 := by
    push_cast
    linear_combination (-12 : K) * h
  exact Nat.cast_ne_zero.2 (by omega) h'

end Grothendieck.Folder147
