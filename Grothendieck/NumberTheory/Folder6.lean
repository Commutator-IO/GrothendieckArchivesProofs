/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
import Grothendieck.Attr

/-!
# Folder 6, pages 49–50: a formal group in no abelian variety, the arithmetic core

The modernised reading `transcripts/6/6.modern.tex` (« Un groupe formel qui ne se plonge dans
aucune variété abélienne », pages 49 and 50) takes a supersingular elliptic curve `E` over a
finite field `k` with `q` elements, all of whose endomorphisms are defined over `k`, and twists
its formal group by a unit `θ` of `𝒜 = End(E) ⊗ ℤ_p`, the maximal order of a quaternion algebra
over `ℚ_p`: the new Frobenius is `φ′ = θ φ`. If the twist embedded in the formal group of an
abelian variety over `k`, the eigenvalues of `φ′` would be algebraic by Weil, so that
« `det φ′ = det φ · det θ` » would be algebraic, hence `det θ`; and
« il est facile de trouver `Θ` unité de `𝒜` tel que `det Θ` ne soit pas algébrique ». The
reading adds that the reduced norm `𝒜* → ℤ_p*` is surjective, that `ℤ_p*` contains
transcendental elements, and that a finite extension of `k` replaces `φ′` by a power, which
changes nothing.

This is finding `6-formal-group-not-in-abelian-variety` of `src/content/findings.ts`. The file
proves the arithmetic of the argument, and nothing about formal groups.

## Main results

### `ℤ_p*` has transcendental elements

* `countable_setOf_isAlgebraic`: for a countable domain `R` (`ℤ` or `ℚ`), the units of `ℤ_p`
  algebraic over `R` form a countable set; `countable_setOf_isAlgebraic_int` and
  `countable_setOf_isAlgebraic_rat` are the two cases.
* `uncountable_units`: `ℤ_p*` is uncountable. With the above, all but countably many units of
  `ℤ_p` are transcendental over `ℚ`.
* `exists_transcendental_unit`: a unit of `ℤ_p` transcendental over `ℚ`.

### The Weil step

* `isAlgebraic_of_mul_isAlgebraic`, `transcendental_mul_isAlgebraic`: in a field `K ⊇ ℚ`, if
  `a ≠ 0` is algebraic over `ℚ`, then `t a` is algebraic iff `t` is. The powers are mathlib's
  `Transcendental.pow`.
* `isAlgebraic_det_of_twist` (p. 50): for a multiplicative map `det : A → K` (the reduced norm,
  or a determinant), if `det φ` is algebraic and nonzero and `det ((θ φ) ^ n)` is algebraic for
  one `n ≥ 1`, then `det θ` is algebraic. `n = 1` is the page's « `det φ′ = det φ · det θ` »,
  `n ≥ 1` the reading's finite extension of `k` (`φ′` replaced by `φ′ ^ n`).
* `transcendental_det_twist_pow`: the contrapositive, as the page uses it: if `det θ` is
  transcendental, no power of `φ′ = θ φ` has an algebraic determinant.

### The norm of the unramified quadratic extension

* `exists_sq_eq_of_toZMod_eq_sq` (Hensel): for `p` odd, a `p`-adic integer whose residue is a
  nonzero square is a square.
* `exists_sq_sub_mul_sq_eq`: for `p` odd and units `u`, `v` of `ℤ_p`, `v = x² − u y²` with
  `x, y ∈ ℤ_p`. For `u` a non-square, `x² − u y²` is the norm of `x + y √u` from `ℤ_p[√u]`, the
  ring of integers of the unramified quadratic extension of `ℚ_p`, so that norm maps the units
  onto `ℤ_p*`.

## Implementation notes

The units of `ℤ_p` are seen in `ℚ_p` through `ℤ_p* → ℤ_p → ℚ_p`. Their uncountability comes from
the unit sphere `‖x‖ = 1` of `ℚ_p`, an open set (the norm is ultrametric), hence of the cardinality
of `ℚ_p`, at least that of the continuum (`continuum_le_cardinal_of_nontriviallyNormedField`); the
algebraic elements are countable by mathlib's `Algebraic.countable`. For the norm form, a solution
modulo `p` (`FiniteField.exists_root_sum_quadratic`) is lifted by Hensel's lemma along whichever
coordinate is nonzero modulo `p`.

## Not formalised

* Formal groups, the forms of `G_{1,1}`, Dieudonné theory, the twist of `Ê` by `θ` and its
  Frobenius `θ φ`, and the embedding into the formal group of an abelian variety.
* Weil's theorem (the eigenvalues of Frobenius are algebraic integers of absolute value `q^{1/2}`):
  `isAlgebraic_det_of_twist` takes the algebraicity of `det (φ′ ^ n)` as a hypothesis.
* The quaternion order `𝒜 = End(E) ⊗ ℤ_p` and its reduced norm: the surjectivity of
  `𝒜* → ℤ_p*` follows from `exists_sq_sub_mul_sq_eq` once `ℤ_p[√u]` (`u` a non-square unit) is
  embedded in `𝒜`, the reduced norm restricting to the norm of `ℤ_p[√u]`; neither the order nor
  the embedding is in mathlib, and `p = 2` is not treated.

## References

* A. Grothendieck, folder 6, pp. 49–50 (finding `6-formal-group-not-in-abelian-variety`);
  modernised reading `transcripts/6/6.modern.tex`
-/

@[expose] public section

namespace Grothendieck.Folder6

open Cardinal Polynomial

/-! ## `ℤ_p*` has transcendental elements -/

section Transcendental

variable {p : ℕ} [Fact p.Prime]

/-- The unit sphere of `ℚ_p` is uncountable. -/
theorem not_countable_sphere : ¬ (Metric.sphere (0 : ℚ_[p]) 1).Countable := fun h ↦
  (aleph0_lt_continuum.trans_le ((continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p]).trans_eq
    (cardinal_eq_of_mem_nhds ℚ_[p] ((IsUltrametricDist.isOpen_sphere 0 one_ne_zero).mem_nhds
      (x := 1) (by simp))).symm)).not_ge (le_aleph0_iff_set_countable.2 h)

/-- Over a countable domain `R`, the units of `ℤ_p` algebraic over `R` form a countable set. -/
@[montpellier "6, 50"]
theorem countable_setOf_isAlgebraic (R : Type*) [CommRing R] [IsDomain R] [Countable R]
    [Algebra R ℚ_[p]] [Module.IsTorsionFree R ℚ_[p]] :
    {u : ℤ_[p]ˣ | IsAlgebraic R (u : ℚ_[p])}.Countable :=
  (Algebraic.countable R ℚ_[p]).preimage (Subtype.val_injective.comp Units.val_injective)

/-- The units of `ℤ_p` algebraic over `ℤ` form a countable set. -/
theorem countable_setOf_isAlgebraic_int :
    {u : ℤ_[p]ˣ | IsAlgebraic ℤ (u : ℚ_[p])}.Countable :=
  countable_setOf_isAlgebraic ℤ

/-- The units of `ℤ_p` algebraic over `ℚ` form a countable set. -/
theorem countable_setOf_isAlgebraic_rat :
    {u : ℤ_[p]ˣ | IsAlgebraic ℚ (u : ℚ_[p])}.Countable :=
  countable_setOf_isAlgebraic ℚ

/-- `ℤ_p*` is uncountable. -/
theorem uncountable_units : Uncountable ℤ_[p]ˣ := by
  refine ⟨fun _ ↦ not_countable_sphere (p := p) ((Set.countable_range
    fun u : ℤ_[p]ˣ ↦ ((u : ℤ_[p]) : ℚ_[p])).mono fun x hx ↦ ?_)⟩
  exact ⟨PadicInt.mkUnits (by simpa using hx), rfl⟩

/-- `ℤ_p*` contains elements transcendental over `ℚ` (the reading's footnote to p. 50). -/
@[montpellier "6, 50"]
theorem exists_transcendental_unit : ∃ u : ℤ_[p]ˣ, Transcendental ℚ (u : ℚ_[p]) := by
  obtain ⟨x, hx, hxa⟩ := Set.not_subset.1 fun h ↦
    not_countable_sphere (p := p) ((Algebraic.countable ℚ ℚ_[p]).mono h)
  exact ⟨PadicInt.mkUnits (by simpa using hx), hxa⟩

end Transcendental

/-! ## The Weil step -/

section Weil

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- If `a ≠ 0` and `t a` are algebraic over `ℚ`, so is `t`. -/
theorem isAlgebraic_of_mul_isAlgebraic {t a : K} (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0)
    (h : IsAlgebraic ℚ (t * a)) : IsAlgebraic ℚ t :=
  ha.of_mul (mem_nonZeroDivisors_of_ne_zero h0) (mul_comm t a ▸ h)

/-- A transcendental element times a nonzero algebraic one is transcendental. -/
theorem transcendental_mul_isAlgebraic {t a : K} (ht : Transcendental ℚ t)
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (t * a) :=
  fun h ↦ ht (isAlgebraic_of_mul_isAlgebraic ha h0 h)

/-- Page 50, « `det φ′ = det φ · det θ` serait algébrique, donc `det θ` aussi », with the
reading's finite extension of `k`: `φ′ = θ φ` is replaced by a power `φ′ ^ n`, `n ≥ 1`. -/
@[montpellier "6, 50"]
theorem isAlgebraic_det_of_twist {A : Type*} [Monoid A] (det : A →* K) {θ φ : A}
    (hφ : IsAlgebraic ℚ (det φ)) (h0 : det φ ≠ 0) {n : ℕ} (hn : 0 < n)
    (h : IsAlgebraic ℚ (det ((θ * φ) ^ n))) : IsAlgebraic ℚ (det θ) := by
  rw [map_pow, map_mul] at h
  exact isAlgebraic_of_mul_isAlgebraic hφ h0 (h.of_pow hn)

/-- If `det θ` is transcendental, no power of the twisted Frobenius `θ φ` has an algebraic
determinant. -/
@[montpellier "6, 50"]
theorem transcendental_det_twist_pow {A : Type*} [Monoid A] (det : A →* K) {θ φ : A}
    (hθ : Transcendental ℚ (det θ)) (hφ : IsAlgebraic ℚ (det φ)) (h0 : det φ ≠ 0) {n : ℕ}
    (hn : 0 < n) : Transcendental ℚ (det ((θ * φ) ^ n)) :=
  fun h ↦ hθ (isAlgebraic_det_of_twist det hφ h0 hn h)

end Weil

/-! ## The norm of the unramified quadratic extension -/

section Norm

variable {p : ℕ} [hp : Fact p.Prime]

/-- Hensel: for `p` odd, a `p`-adic integer whose residue is a nonzero square is a square. -/
theorem exists_sq_eq_of_toZMod_eq_sq (hp2 : p ≠ 2) {w : ℤ_[p]} {c : ZMod p} (hc : c ≠ 0)
    (h : PadicInt.toZMod w = c ^ 2) : ∃ x, x ^ 2 = w := by
  have hker {y : ℤ_[p]} : PadicInt.toZMod y = 0 ↔ ‖y‖ < 1 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
      PadicInt.mem_nonunits]
  set a : ℤ_[p] := (c.val : ℤ_[p])
  have ha : PadicInt.toZMod a = c := by simp [a]
  have h1 : ‖a‖ = 1 := (PadicInt.norm_le_one a).antisymm (not_lt.1 fun h' ↦ hc (ha ▸ hker.2 h'))
  have h2 : ‖(2 : ℤ_[p])‖ = 1 := mod_cast PadicInt.norm_natCast_eq_one_iff.2
    ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
  obtain ⟨x, hx, -⟩ := hensels_lemma (F := X ^ 2 - C w) (a := a) (by
    simpa [h1, one_add_one_eq_two, h2] using (hker (y := a ^ 2 - w)).1 (by simp [ha, h]))
  exact ⟨x, by simpa [sub_eq_zero] using hx⟩

/-- For `p` odd, every unit `v` of `ℤ_p` is `x² − u y²` for a given unit `u`: for `u` a
non-square, the norm of `ℤ_p[√u]` maps its units onto `ℤ_p*`. -/
@[montpellier "6, 50"]
theorem exists_sq_sub_mul_sq_eq (hp2 : p ≠ 2) (u v : ℤ_[p]ˣ) :
    ∃ x y : ℤ_[p], x ^ 2 - u * y ^ 2 = v := by
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    simpa [Nat.odd_iff] using hp.out.odd_of_ne_two hp2
  have hu := (u.isUnit.map (PadicInt.toZMod (p := p))).ne_zero
  have hv := (v.isUnit.map (PadicInt.toZMod (p := p))).ne_zero
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (degree_X_pow_sub_C two_pos (PadicInt.toZMod (v : ℤ_[p])))
    (degree_C_mul_X_pow 2 (neg_ne_zero.2 hu)) hodd
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hab
  by_cases ha : a = 0
  · subst ha
    obtain ⟨y, hy⟩ := exists_sq_eq_of_toZMod_eq_sq hp2 (w := -(v * ↑u⁻¹)) (c := b)
      (by rintro rfl; exact hv (by simpa using hab)) (by simp; field_simp; linear_combination hab)
    exact ⟨0, y, by rw [hy]; linear_combination (v : ℤ_[p]) * u.mul_inv⟩
  · obtain ⟨x, hx⟩ := exists_sq_eq_of_toZMod_eq_sq hp2 (w := v + u * (b.val : ℤ_[p]) ^ 2) ha
      (by simp; linear_combination -hab)
    exact ⟨x, b.val, by rw [hx]; ring⟩

end Norm

end Grothendieck.Folder6
