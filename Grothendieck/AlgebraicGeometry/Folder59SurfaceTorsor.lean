/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Ring
import Grothendieck.Attr

/-!
# Folder 59, pages 11–13: the torsor `Pic^δ` of an abelian surface with `χ(δ)` even

Finding `59-surface-even-chi-torsor`. For `A/S` an abelian scheme of relative dimension `n`,
`B` its dual and `δ` a section of `NS(A/S)`, `Pic^δ_{A/S}` is a torsor under `B`; let `c` be its
class in `H¹(S, B)`, written additively. Let `δ′` on `B` be the dual class, `δ″` on `A` the dual
of `δ′`, and `δ̃ : A → B`, `δ̃′ : B → A`, `δ̃″ : A → B` the associated homomorphisms. Page 13
composes the canonical isomorphism `(*) Pic^{δ′}_{B/S} ≃ δ̃′_* Pic^δ_{A/S}` with its analogue
`Pic^{δ″}_{A/S} ≃ δ̃″_* Pic^{δ′}_{B/S}`, and uses `δ″ = χ(δ)^{n−2} δ` and
`δ̃″ δ̃′ = χ(δ)^{n−1}`: the class `χ(δ)^{n−1} c` of `(δ̃″ δ̃′)_* Pic^δ` is the class
`χ(δ)^{n−2} c` of `Pic^{δ″}`, so `χ(δ)^{n−2}(χ(δ) − 1) c = 0`. With `2 χ(δ)^{n−2} c = 0` and
`χ(δ) − 1` odd when `χ(δ)` is even, `χ(δ)^{n−2} c = 0`; for `n = 2`, `c = 0`: the torsor is trivial.

**The statement on abelian schemes is not proved here.** Abelian schemes, the dual `B`, `NS`,
`Pic^δ`, the torsor classes in `H¹(S, B)`, the isomorphism `(*)` and the identities
`δ″ = χ(δ)^{n−2} δ`, `δ̃″ δ̃′ = χ(δ)^{n−1}` and `2 χ(δ)^{n−2} c = 0` are not formalised. What is
proved is the arithmetic of page 13 in an abelian group, and the composition step for abstract
homomorphisms, with these facts as hypotheses.

## The page's arithmetic

Checked by hand before the formalisation, and it comes out: `χ^{n−1} − χ^{n−2} = χ^{n−2}(χ − 1)`
for `n ≥ 2`; `gcd(χ^{n−2}(χ − 1), 2 χ^{n−2}) = χ^{n−2} gcd(χ − 1, 2)`, so an element killed by both
is killed by `χ^{n−2} gcd(χ − 1, 2)`; for `χ` even `gcd(χ − 1, 2) = 1`, and for `n = 2`,
`χ^{n−2} = 1`. The bound `n ≥ 2` is needed for the first identity (for `n = 1` the natural
subtractions give `χ^0 − χ^0 = 0`), and the page is in that range.

## Main results

* `zsmul_eq_zero_of_gcd` (p. 13): in an additive commutative group, if
  `χ^{n−2}(χ − 1) • c = 0` and `2 χ^{n−2} • c = 0`, then `χ^{n−2} gcd(χ − 1, 2) • c = 0`.
* `pow_zsmul_eq_zero_of_even` (p. 13): if moreover `χ` is even, `χ^{n−2} • c = 0`.
* `eq_zero_of_even` (p. 13, `n = 2`): `(χ − 1) • c = 0`, `2 • c = 0` and `χ` even give `c = 0`.
* `zsmul_sub_one_eq_zero_of_comp` (p. 13, the composition step): for homomorphisms
  `f′ : G_B → G_A`, `f″ : G_A → G_B` with `f″ ∘ f′ = χ^{n−1}` and classes `c, c′, c″` with
  `c′ = f′ c` (`(*)` for `δ`), `c″ = f″ c′` (`(*)` for `δ′`) and `c″ = χ^{n−2} • c`
  (`δ″ = χ^{n−2} δ`), `χ^{n−2}(χ − 1) • c = 0`.
* `eq_zero_of_comp_of_even` (pp. 11–13, `n = 2`): the same hypotheses with `n = 2`, `2 • c = 0`
  and `χ` even give `c = 0`.

## Implementation notes

`G_B` and `G_A` stand for `H¹(S, B)` and `H¹(S, A)`, `f′` and `f″` for the maps `δ̃′_*` and
`δ̃″_*` induced on them. The hypothesis `f″ ∘ f′ = χ^{n−1}` packs the functoriality of `H¹`
(`(δ̃″ δ̃′)_* = δ̃″_* δ̃′_*`, and multiplication by `m` on `B` induces multiplication by `m`) with
`δ̃″ δ̃′ = χ^{n−1}`; the hypothesis `c″ = χ^{n−2} • c` packs `δ″ = χ^{n−2} δ` with the fact that
the class of `Pic^{mδ}` is `m` times that of `Pic^δ` (`L ↦ L^{⊗m}`). `χ` is an integer and `n` a
natural number, the exponents `n − 2`, `n − 1` natural subtractions.

## Not formalised

* Abelian schemes, their duals, `NS`, `Pic^δ`, `χ(δ)`, `H¹(S, −)` and its functoriality.
* The isomorphism `(*)`, the identities `δ″ = χ(δ)^{n−2} δ` and `δ̃″ δ̃′ = χ(δ)^{n−1}`, and the
  vanishing of `2 χ(δ)^{n−2} c`: hypotheses.

## References

* A. Grothendieck, folder 59, pp. 11–13 (finding `59-surface-even-chi-torsor`)
-/

@[expose] public section

namespace Grothendieck.Folder59

variable {G : Type*} [AddCommGroup G]

/-- `59-surface-even-chi-torsor` (folder 59, p. 13): an element `c` of an additive commutative
group (the class of `Pic^δ` in `H¹(S, B)`) killed by `χ^{n−2}(χ − 1)` and by `2 χ^{n−2}` is killed
by `χ^{n−2} gcd(χ − 1, 2)`. -/
@[montpellier "59, 13"]
theorem zsmul_eq_zero_of_gcd {χ : ℤ} {n : ℕ} {c : G} (h₁ : (χ ^ (n - 2) * (χ - 1)) • c = 0)
    (h₂ : (2 * χ ^ (n - 2)) • c = 0) : (χ ^ (n - 2) * (Int.gcd (χ - 1) 2 : ℤ)) • c = 0 := by
  rw [Int.gcd_eq_gcd_ab, show χ ^ (n - 2) * ((χ - 1) * Int.gcdA (χ - 1) 2 + 2 * Int.gcdB (χ - 1) 2)
    = Int.gcdA (χ - 1) 2 * (χ ^ (n - 2) * (χ - 1)) + Int.gcdB (χ - 1) 2 * (2 * χ ^ (n - 2)) by ring,
    add_smul, mul_smul _ (χ ^ (n - 2) * (χ - 1)), mul_smul _ (2 * χ ^ (n - 2)), h₁, h₂, smul_zero,
    smul_zero, add_zero]

/-- `59-surface-even-chi-torsor` (folder 59, p. 13): if moreover `χ` is even, `χ − 1` is odd, so
`gcd(χ − 1, 2) = 1` and `χ^{n−2} • c = 0`. -/
@[montpellier "59, 13"]
theorem pow_zsmul_eq_zero_of_even {χ : ℤ} {n : ℕ} {c : G} (hχ : Even χ)
    (h₁ : (χ ^ (n - 2) * (χ - 1)) • c = 0) (h₂ : (2 * χ ^ (n - 2)) • c = 0) :
    χ ^ (n - 2) • c = 0 := by
  have h : Int.gcd (χ - 1) 2 = 1 := by
    obtain ⟨r, rfl⟩ := hχ
    exact Int.isCoprime_iff_gcd_eq_one.mp ⟨-1, r, by ring⟩
  simpa [h] using zsmul_eq_zero_of_gcd h₁ h₂

/-- `59-surface-even-chi-torsor` (folder 59, p. 13), for `n = 2`: if `(χ − 1) • c = 0`,
`2 • c = 0` and `χ` is even, then `c = 0`. -/
@[montpellier "59, 13"]
theorem eq_zero_of_even {χ : ℤ} {c : G} (hχ : Even χ) (h₁ : (χ - 1) • c = 0)
    (h₂ : (2 : ℤ) • c = 0) : c = 0 := by
  simpa using pow_zsmul_eq_zero_of_even (n := 2) hχ (by simpa using h₁) (by simpa using h₂)

variable {G' : Type*} [AddCommGroup G']

/-- `59-surface-even-chi-torsor` (folder 59, p. 13), the composition step. `G` and `G'` stand for
`H¹(S, B)` and `H¹(S, A)`, `f′` and `f″` for `δ̃′_*` and `δ̃″_*`, `c`, `c′`, `c″` for the classes of
`Pic^δ_{A/S}`, `Pic^{δ′}_{B/S}`, `Pic^{δ″}_{A/S}`. Hypotheses: `f″ ∘ f′ = χ^{n−1}`
(`δ̃″ δ̃′ = χ(δ)^{n−1}` and the functoriality of `H¹`), `c′ = f′ c` (`(*)` for `δ`),
`c″ = f″ c′` (`(*)` for `δ′`) and `c″ = χ^{n−2} • c` (`δ″ = χ(δ)^{n−2} δ`, and the class of
`Pic^{mδ}` is `m` times that of `Pic^δ`). Conclusion: `χ^{n−2}(χ − 1) • c = 0`. -/
@[montpellier "59, 13"]
theorem zsmul_sub_one_eq_zero_of_comp {χ : ℤ} {n : ℕ} (hn : 2 ≤ n) (f' : G →+ G')
    (f'' : G' →+ G) (hf : ∀ x, f'' (f' x) = χ ^ (n - 1) • x) {c : G} {c' : G'} {c'' : G}
    (h' : c' = f' c) (h'' : c'' = f'' c') (hδ : c'' = χ ^ (n - 2) • c) :
    (χ ^ (n - 2) * (χ - 1)) • c = 0 := by
  have hχ : χ ^ (n - 1) = χ ^ (n - 2) * χ := by rw [← pow_succ]; congr 1; omega
  rw [mul_sub, mul_one, sub_smul, ← hχ, ← hf, ← h', ← h'', hδ, sub_self]

/-- `59-surface-even-chi-torsor` (folder 59, pp. 11–13), relative dimension `n = 2`: with the
hypotheses of `zsmul_sub_one_eq_zero_of_comp` for `n = 2` (`f″ ∘ f′ = χ`, `c″ = c`), `2 • c = 0`
and `χ` even, the class `c` of `Pic^δ_{A/S}` is `0`: the torsor is trivial. -/
@[montpellier "59, 11–13"]
theorem eq_zero_of_comp_of_even {χ : ℤ} (hχ : Even χ) (f' : G →+ G') (f'' : G' →+ G)
    (hf : ∀ x, f'' (f' x) = χ • x) {c : G} {c' : G'} {c'' : G} (h' : c' = f' c)
    (h'' : c'' = f'' c') (hδ : c'' = c) (h₂ : (2 : ℤ) • c = 0) : c = 0 := by
  have h := zsmul_sub_one_eq_zero_of_comp (n := 2) le_rfl f' f'' (by simpa using hf) h' h''
    (by simpa using hδ)
  exact eq_zero_of_even hχ (by simpa using h) h₂

end Grothendieck.Folder59
