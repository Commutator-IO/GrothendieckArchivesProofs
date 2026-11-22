module

public import StacksFrontier.RingTheory.DeRham.Cartier.Coordinates
public import Grothendieck.AlgebraicGeometry.Folder93

@[expose] public section

/-!
# Folder 93: Cartier descent in rank one on an algebra with Frobenius coordinates

`Grothendieck/AlgebraicGeometry/Folder93.lean` proves Cartier's converse in rank one
(`horizontal_generate`) for a derivation `D` with `Dᵖ = 0` and an element `x` with `D x = 1`, as
`d/dx` on `𝔽_p[x]`; the passage to a smooth curve was left out (« la descente de Cartier n'est
formalisée que sur le fibré trivial, quand l'anneau a une coordonnée »).

The vendored AxiomMath/Stacks file `StacksFrontier/RingTheory/DeRham/Cartier/Coordinates.lean`
supplies the setting of a smooth algebra in characteristic `p` with coordinates: **Frobenius
coordinates** `t₁, …, tₙ` of `B` over `A` (`KaehlerDifferential.Cartier.IsFrobeniusCoordinates`:
the monomials `t^α`, `0 ≤ αⱼ < p`, form a basis of `B` over its `p`-th powers), with the
differentials `dt₁, …, dtₙ` a basis of `Ω[B⁄A]`. A polynomial algebra over a perfect ring has
them, and so does an algebra étale over one; the same file proves the Cartier isomorphism for
them.

**What is proved.** For a basis `b` of `Ω[B⁄A]` with `b j = dtⱼ`:
* `partialD`: the partial derivative `∂/∂tⱼ`, the coordinate of `d y` along `dtⱼ`;
* `partialD_t`: `∂tₗ/∂tⱼ = δₗⱼ`;
* `partialD_iterate_p_eq_zero`: `(∂/∂tⱼ)ᵖ = 0` on `B`. It kills the `p`-th powers and lowers
  the exponent of `tⱼ` in `c^p t^α` by one, with the factor `αⱼ`; after `p` steps the factor is
  the descending factorial of `αⱼ < p` over `p` terms, which vanishes;
* `horizontal_generate_of_frobeniusCoordinates` (Cartier descent in rank one): for every
  `a ∈ B` whose connection `∂/∂tⱼ + a` has zero `p`-curvature, `aᵖ + (∂/∂tⱼ)^{p-1} a = 0`, the
  horizontal sections generate `B`. This is `Folder93.horizontal_generate` with `x = tⱼ`.

Not formalised: Cartier descent for a connection in several variables at once (integrable,
all `p`-curvatures zero), for a nontrivial line bundle, and in higher rank on such an algebra.
-/

namespace Grothendieck.Folder93.Frobenius

open KaehlerDifferential KaehlerDifferential.Cartier Finset

universe u

variable {p : ℕ} [hp : Fact p.Prime] {A : Type u} {B : Type u} [CommRing A] [CommRing B]
  [Algebra A B] [CharP B p] {n : ℕ} {t : Fin n → B}
  (b : Module.Basis (Fin n) B (Ω[B⁄A])) (hb : ∀ j, b j = KaehlerDifferential.D A B (t j))

/-- The partial derivative `∂/∂tⱼ`: the coordinate of `d y` along `dtⱼ` in the basis `b`. -/
noncomputable def partialD (j : Fin n) : Derivation A B B :=
  (b.coord j).compDer (KaehlerDifferential.D A B)

omit hp [CharP B p] in
theorem partialD_apply (j : Fin n) (y : B) :
    partialD b j y = b.coord j (KaehlerDifferential.D A B y) := rfl

include hb in
omit hp [CharP B p] in
/-- `∂tₗ/∂tⱼ = δₗⱼ`. -/
theorem partialD_t (j l : Fin n) : partialD b j (t l) = if l = j then 1 else 0 := by
  rw [partialD_apply, ← hb, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

include hb in
omit hp [CharP B p] in
/-- `∂tⱼ/∂tⱼ = 1`. -/
theorem partialD_t_self (j : Fin n) : partialD b j (t j) = 1 := by
  simp [partialD_t b hb]

include hb in
omit hp [CharP B p] in
/-- `∂tₗ/∂tⱼ = 0` for `l ≠ j`. -/
theorem partialD_t_of_ne {j l : Fin n} (h : l ≠ j) : partialD b j (t l) = 0 := by
  simp [partialD_t b hb, h]

omit hp in
/-- `∂/∂tⱼ` kills `p`-th powers. -/
theorem partialD_pow_p (j : Fin n) (c : B) : partialD b j (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, CharP.cast_eq_zero, zero_smul]

include hb in
omit hp [CharP B p] in
/-- A product of powers of the other coordinates is killed by `∂/∂tⱼ`. -/
theorem partialD_prod_eq_zero (j : Fin n) (a : Fin n → ℕ) (s : Finset (Fin n)) (hs : j ∉ s) :
    partialD b j (∏ l ∈ s, t l ^ a l) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih =>
    have hlj : ¬ l = j := by
      rintro rfl
      exact hs (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hl, Derivation.leibniz, Derivation.leibniz_pow, partialD_t_of_ne b hb hlj, ih (fun h => hs (Finset.mem_insert_of_mem h))]
    simp

include hb in
omit hp [CharP B p] in
/-- `∂(Q tⱼ^m) = m Q tⱼ^{m-1}` when `∂Q = 0`. -/
theorem partialD_mul_pow (j : Fin n) (Q : B) (hQ : partialD b j Q = 0) (m : ℕ) :
    partialD b j (Q * t j ^ m) = Q * (m : B) * t j ^ (m - 1) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, partialD_t_self b hb, hQ]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
  ring

include hb in
omit hp [CharP B p] in
/-- `∂^k(Q tⱼ^a) = a(a-1)⋯(a-k+1) Q tⱼ^{a-k}` when `∂Q = 0`. -/
theorem partialD_iterate (j : Fin n) (Q : B) (hQ : partialD b j Q = 0) (a k : ℕ) :
    (⇑(partialD b j))^[k] (Q * t j ^ a) = Q * (a.descFactorial k : B) * t j ^ (a - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hQ' : partialD b j (Q * (a.descFactorial k : B)) = 0 := by
      rw [Derivation.leibniz, hQ, Derivation.map_natCast]
      simp
    rw [Function.iterate_succ_apply', ih, partialD_mul_pow b hb j _ hQ', Nat.descFactorial_succ,
      Nat.sub_sub]
    push_cast
    ring

include hb in
omit hp in
/-- **`(∂/∂tⱼ)ᵖ = 0`** for Frobenius coordinates. -/
theorem partialD_iterate_p_eq_zero (hF : IsFrobeniusCoordinates p B t) (j : Fin n) (y : B) :
    (⇑(partialD b j))^[p] y = 0 := by
  obtain ⟨c, rfl⟩ := hF.2 y
  let f : AddMonoid.End B := (partialD b j : B →ₗ[A] B).toAddMonoidHom
  have hf : (⇑(partialD b j))^[p] = ⇑(f ^ p) := by
    rw [AddMonoid.End.coe_pow]
    rfl
  rw [hf, map_sum, ← hf]
  refine Finset.sum_eq_zero fun α _ => ?_
  have hsplit : c α ^ p * monomial t (fun l ↦ (α l : ℕ)) =
      (c α ^ p * ∏ l ∈ univ.erase j, t l ^ (α l : ℕ)) * t j ^ (α j : ℕ) := by
    rw [monomial, ← Finset.mul_prod_erase univ (fun l ↦ t l ^ (α l : ℕ)) (mem_univ j)]
    ring
  have hQ : partialD b j (c α ^ p * ∏ l ∈ univ.erase j, t l ^ (α l : ℕ)) = 0 := by
    rw [Derivation.leibniz, partialD_pow_p b j,
      partialD_prod_eq_zero b hb j _ _ (Finset.notMem_erase j univ)]
    simp
  rw [hsplit, partialD_iterate b hb j _ hQ,
    Nat.descFactorial_eq_zero_iff_lt.2 (α j).isLt, Nat.cast_zero, mul_zero, zero_mul]

include hb in
/-- **Cartier descent in rank one on an algebra with Frobenius coordinates.** If the connection
`∂/∂tⱼ + a` has zero `p`-curvature, `aᵖ + (∂/∂tⱼ)^{p-1} a = 0`, its horizontal sections
generate `B`: `∑_{i<p} tⱼ^i/i! yᵢ = 1` with `∂yᵢ/∂tⱼ + a yᵢ = 0`. -/
theorem horizontal_generate_of_frobeniusCoordinates (hF : IsFrobeniusCoordinates p B t)
    (j : Fin n) (a : B) (hψ : a ^ p + (⇑(partialD b j))^[p - 1] a = 0) :
    ∃ y : ℕ → B, ∑ i ∈ range p, t j ^ i * PCurvature.u (A := B) i * y i = 1 ∧
      ∀ i, partialD b j (y i) + a * y i = 0 :=
  PCurvature.horizontal_generate ((partialD b j).restrictScalars ℤ) p
    (partialD_iterate_p_eq_zero b hb hF j) (t j) (partialD_t_self b hb j) a hψ

end Grothendieck.Folder93.Frobenius
