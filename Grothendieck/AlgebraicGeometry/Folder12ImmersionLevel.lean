/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Order.Basic
import Grothendieck.Attr

/-!
# Folder 12, pages 115, 117, 119: weight and level of `Rⁱf_* ℚ_ℓ` for an immersion, the count

Finding `12-immersion-level-bound`. For an immersion `f : X → Y`, `X` regular,
`n = dim \overline{f(X)}`, page 119 boxes: the constituents of `Rⁱf_* ℚ_ℓ` have weight
`≤ 2 inf(i, n)` and level `≤ inf(i, n − 1)`. Page 115 factors `f = h ∘ g`, `g` an open
immersion into a regular `Y′` with normal-crossings complement `Z = Σ Zᵢ`, `h` proper, and bounds
each term of `E₂^{pq} = R^p h_*(R^q g_* ℚ_ℓ) ⇒ R^{p+q} f_* ℚ_ℓ`:

* `E₂^{p0} = R^p h_* ℚ_ℓ`: weight `≤ p`, level `≤ inf(p, 2n − 2 − p)`;
* `E₂^{pq}`, a sum of `R^p h_*` of `ℚ_ℓ(−q)` on the `q`-fold intersections: weight
  `≤ p + 2q`, level `≤ inf(p, 2n − 2q − p)`;
* in the margin, « (5.e) »: `p ≤ 2(n − q)`, boxed as `p + 2q ≤ 2n`.

Pages 117 and 119 tabulate these by rows `E₂^{i−q,q}` for `i ≤ n − 1` and `i ≥ n`.

**The geometry is not formalised.** Étale cohomology, `ℚ_ℓ`-sheaves, weights, levels, the
factorisation (which rests on resolution), purity, the spectral sequence and the passage of the
bounds from `E₂` to the abutment (« effectively admissible » stable under subquotients and
extensions, not written on these sheets) are **hypotheses**: the structure `PageBounds` records
the three bounds of page 115 above for abstract data `nz p q` (« `E₂^{pq} ≠ 0` »), `wt p q`,
`lv p q` (weight and level of `E₂^{pq}`), and a constituent of `Rⁱf_*` is assumed to come from
some `E₂^{p,q}` with `p + q = i`. What is proved is the count over `ℕ`, for all `i` and `n`.

## Main definitions

* `PageBounds n nz wt lv`: the three bounds of page 115, as hypotheses.

## Main results

* `weight_le`, `level_le_sharp`, `level_le`, `boxed` (pp. 115, 119): from the bounds of page 115,
  every `E₂^{p,q}` with `p + q = i` has weight `≤ 2 inf(i, n)` and level `≤ inf(i, 2n − 1 − i)`,
  hence `≤ inf(i, n − 1)`; the boxed bound of page 119 for a constituent of `Rⁱf_*`.
* `exists_weight_eq`, `exists_level_eq`: the maxima are attained by the bounds of page 115 (for
  `i ≤ 2n − 1`), so `inf(i, 2n − 1 − i)` is exactly the level row of the framed table of p. 119
  (`0, 1, …, n − 1, n − 1, n − 2, …, 0` for `i = 0, …, 2n − 1`).
* `weight_eq_two_mul` (p. 119): weight `2n` is reached only by `E₂^{2(i−n), 2n−i}`, of level
  bound `0`.
* `level_add_one_eq` (the « one less than `2n − i` » of the claim): for `n ≤ i < 2n`, the level
  bound is `2n − 1 − i`, one less than `2n − i`.
* `not_summary_bound` (p. 115): the summary line of page 115, « niveau `≤ Inf(i, 2n − 2 − i)` »,
  does **not** follow from the page's own bounds: `E₂^{1,1}` for `n = 2` allows level `1`
  where it gives `0`. Page 119 has `n − 1`, not `n − 2`, at `i = n`.
* `level_zero_general`: with the general formula `inf(p, 2n − 2q − p)` at `q = 0` in place of
  `inf(p, 2n − 2 − p)`, the term `E₂^{n,0}` would allow level `n > n − 1`: the bound
  `2n − 2 − p` that page 115 writes for `E₂^{p0}` is what gives `n − 1`.

## Not formalised

* Everything geometric listed above; the lower bounds on the weights in the tables of pp. 117
  and 119 (`2(i − n + 1)`, …) and the pairing of each weight with a level column by column (the
  last columns are overwritten, and the transcription gives them unverified).
* The two extensions of p. 119 with « ? »: `F` strictly special of weight `j`, and the relative
  case `n = d_y(f)`.

## References

* A. Grothendieck, folder 12, pp. 115, 117, 119 (finding `12-immersion-level-bound`)
-/

@[expose] public section

namespace Grothendieck.Folder12

/-- The bounds of page 115 on the terms `E₂^{pq}` of `R^p h_*(R^q g_* ℚ_ℓ) ⇒ R^{p+q} f_* ℚ_ℓ`, as
hypotheses on abstract data: `nz p q` stands for `E₂^{pq} ≠ 0`, `wt p q` and `lv p q` for its
weight and level. Subtraction is truncated, which only weakens the hypotheses. -/
structure PageBounds (n : ℕ) (nz : ℕ → ℕ → Prop) (wt lv : ℕ → ℕ → ℕ) : Prop where
  /-- The margin « (5.e) »: `p ≤ 2(n − q)`, i.e. `p + 2q ≤ 2n`. -/
  support : ∀ p q, nz p q → p + 2 * q ≤ 2 * n
  /-- `E₂^{pq}` is of weight `≤ p + 2q`. -/
  weight : ∀ p q, nz p q → wt p q ≤ p + 2 * q
  /-- `E₂^{p0} = R^p h_* ℚ_ℓ` is of level `≤ inf(p, 2n − 2 − p)`. -/
  level_zero : ∀ p, nz p 0 → lv p 0 ≤ min p (2 * n - 2 - p)
  /-- `E₂^{pq}`, `q ≥ 1`, is of level `≤ inf(p, 2n − 2q − p)`. -/
  level_pos : ∀ p q, 0 < q → nz p q → lv p q ≤ min p (2 * n - 2 * q - p)

variable {n i p q : ℕ} {nz : ℕ → ℕ → Prop} {wt lv : ℕ → ℕ → ℕ}

/-- `12-immersion-level-bound` (folder 12, pp. 115, 119): every `E₂^{p,q}` with `p + q = i` has
weight `≤ 2 inf(i, n)`. -/
@[montpellier "12, 115, 119"]
theorem weight_le (h : PageBounds n nz wt lv) (hi : p + q = i) (hpq : nz p q) :
    wt p q ≤ 2 * min i n := by
  have := h.support p q hpq
  have := h.weight p q hpq
  omega

/-- `12-immersion-level-bound` (folder 12, pp. 115, 119): every `E₂^{p,q}` with `p + q = i` has
level `≤ inf(i, 2n − 1 − i)`, the level row of the framed table of page 119. -/
@[montpellier "12, 115, 119"]
theorem level_le_sharp (h : PageBounds n nz wt lv) (hi : p + q = i) (hpq : nz p q) :
    lv p q ≤ min i (2 * n - 1 - i) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have := h.level_zero p hpq
    omega
  · have := h.level_pos p q hq hpq
    omega

/-- `12-immersion-level-bound` (folder 12, pp. 115, 119): every `E₂^{p,q}` with `p + q = i` has
level `≤ inf(i, n − 1)`. -/
@[montpellier "12, 115, 119"]
theorem level_le (h : PageBounds n nz wt lv) (hi : p + q = i) (hpq : nz p q) :
    lv p q ≤ min i (n - 1) := by
  have := level_le_sharp h hi hpq
  omega

/-- `12-immersion-level-bound` (folder 12, p. 119, boxed): a constituent of `Rⁱf_* ℚ_ℓ` of weight
`w` and level `l`, coming from some `E₂^{p,q}` with `p + q = i` (hypothesis: the passage to the
abutment is not on the sheets), has weight `≤ 2 inf(i, n)` and level `≤ inf(i, n − 1)`. -/
@[montpellier "12, 115, 119"]
theorem boxed (h : PageBounds n nz wt lv) {w l : ℕ}
    (hc : ∃ p q, p + q = i ∧ nz p q ∧ w ≤ wt p q ∧ l ≤ lv p q) :
    w ≤ 2 * min i n ∧ l ≤ min i (n - 1) := by
  obtain ⟨p, q, hi, hpq, hw, hl⟩ := hc
  exact ⟨Nat.le_trans hw (weight_le h hi hpq), Nat.le_trans hl (level_le h hi hpq)⟩

/-- The weight bound `2 inf(i, n)` is attained by the bounds of page 115 for `i ≤ 2n − 1`: at
`E₂^{0,i}` for `i ≤ n`, at `E₂^{2(i−n), 2n−i}` for `i ≥ n`. -/
@[montpellier "12, 117, 119"]
theorem exists_weight_eq (hi : i < 2 * n) :
    ∃ p q, p + q = i ∧ p + 2 * q ≤ 2 * n ∧ p + 2 * q = 2 * min i n := by
  rcases Nat.le_total i n with h | h
  · exact ⟨0, i, by omega, by omega, by omega⟩
  · exact ⟨2 * (i - n), 2 * n - i, by omega, by omega, by omega⟩

/-- The level bound `inf(i, 2n − 1 − i)` is attained by the bounds of page 115 for `i ≤ 2n − 1`:
at `E₂^{i,0}` for `i ≤ n − 1`, at `E₂^{i−1,1}` for `i ≥ n`. -/
@[montpellier "12, 115, 117, 119"]
theorem exists_level_eq (hi : i < 2 * n) :
    ∃ p q, p + q = i ∧ p + 2 * q ≤ 2 * n ∧
      (if q = 0 then min p (2 * n - 2 - p) else min p (2 * n - 2 * q - p)) =
        min i (2 * n - 1 - i) := by
  rcases Nat.lt_or_ge i n with h | h
  · exact ⟨i, 0, by omega, by omega, by simp; omega⟩
  · exact ⟨i - 1, 1, by omega, by omega, by simp; omega⟩

/-- `12-immersion-level-bound` (folder 12, p. 119): for `i ≥ n`, weight `2n` occurs only at
`E₂^{2(i−n), 2n−i}`, of level bound `0` (the levels « fall back to `0` at weight `2n` »). -/
@[montpellier "12, 117, 119"]
theorem weight_eq_two_mul (hq : 0 < q) (hi : p + q = i) (hw : p + 2 * q = 2 * n) :
    q = 2 * n - i ∧ p = 2 * (i - n) ∧ min p (2 * n - 2 * q - p) = 0 := by
  omega

/-- The « one less than `2n − i` » of the claim: for `n ≤ i < 2n`, the level bound
`inf(i, 2n − 1 − i)` is `2n − 1 − i`, and adding one gives `2n − i`, the level allowed for `Hⁱ`
of a smooth variety of dimension `n`. -/
@[montpellier "12, 119"]
theorem level_add_one_eq (hn : n ≤ i) (hi : i < 2 * n) :
    min i (2 * n - 1 - i) = 2 * n - 1 - i ∧ 2 * n - 1 - i + 1 = 2 * n - i := by
  omega

/-- `12-immersion-level-bound` (folder 12, p. 115): the summary line « niveau
`≤ Inf(i, 2n − 2 − i)` » of page 115 does not follow from the page's bound on `E₂^{pq}`:
for `n = 2`, `E₂^{1,1}` satisfies the margin's `p + 2q ≤ 2n` and has level bound
`inf(1, 2n − 2 − 1) = 1`, while `inf(i, 2n − 2 − i) = 0` for `i = 2`. -/
@[montpellier "12, 115"]
theorem not_summary_bound :
    ¬ ∀ n p q, 0 < q → p + 2 * q ≤ 2 * n →
      min p (2 * n - 2 * q - p) ≤ min (p + q) (2 * n - 2 - (p + q)) := by
  intro h
  have := h 2 1 1 (by decide) (by decide)
  simp at this

/-- With the general formula `inf(p, 2n − 2q − p)` taken at `q = 0`, the term `E₂^{n,0}` would
allow level `n`, above the boxed `n − 1`; page 115 writes `inf(p, 2n − 2 − p)` for `E₂^{p0}`,
which gives `n − 2` there. -/
@[montpellier "12, 115"]
theorem level_zero_general (hn : 0 < n) :
    min n (2 * n - 2 * 0 - n) = n ∧ min n (n - 1) < n ∧ min n (2 * n - 2 - n) = n - 2 := by
  omega

end Grothendieck.Folder12
