/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
import Grothendieck.Attr

/-!
# Abelian varieties and reductive groups: the open problems, stated as propositions

Section « Abelian varieties and reductive groups » of the note on the open problems of the
Montpellier notes (`docs/problems/article.tex`): problems p:surf and p:kostant. Nothing here is
proved; a `def … : Prop` asserts nothing.

## Main definitions

* `KostantOppositeTypeA` (p:kostant): the question of general position, for the groups of type
  `A_{n-1}` (`G = PGL_n(ℂ)`) only. A special case. Proved for every `n`:
  `Grothendieck.Folder123KostantOpposite.kostantOppositeTypeA`
  (`Grothendieck/Folder123KostantOpposite.lean`).
* `KostantOppositeTypeC`, `KostantOppositeTypeB`, `KostantOppositeTypeD` (p:kostant): the same
  question for `Sp_{2n}`, `SO_{2n+1}`, `SO_{2n}` in their standard matrix models (the form pairing
  `e_i` with `e_{N-1-i}`, Kostant's cyclic element `cyclicElementC`, `cyclicElementB`,
  `cyclicElementD`). Proved in `Grothendieck/Folder123KostantClassical.lean`: in types `C` and
  `B` every `E'`-stable complete flag is opposite to the standard one; in type `D` the isotropic
  steps `V_k`, `k < n`, are transverse, and the middle step holds for one of the two maximal
  isotropic subspaces through `V_{n-1}` only (so it is not in the statement).

## Not formalised

* p:surf (is `Pic^δ_{A/S}` a trivial torsor under the dual `B` when `A/S` is an abelian scheme of
  relative dimension 2 and `χ(δ)` is even?). Stacks has abelian varieties over a field
  (`IsAbelianVariety`) and abelian schemes (`IsAbelianScheme`), but not the dual abelian scheme
  `Pic⁰_{A/S}`, the Néron–Severi sheaf `NS_{A/S}`, the torsors `Pic^δ_{A/S}`, or the Euler
  characteristic `χ(δ)` of a class; the Poonen–Stoll class `c_δ ∈ H¹(k, B)` needs all of them.
  Over a field the question reads: for an abelian surface `A/k` and a Galois-invariant class `δ`
  of `NS(A_{k̄})` with `χ(δ)` even, is `δ` the class of a line bundle defined over `k`? Even that
  needs `NS` of a base change and its Galois action.
* p:kostant in general (any simple adjoint group), in particular the exceptional types
  `E₆, E₇, E₈, F₄, G₂`: Mathlib has Lie algebras, Cartan subalgebras and root systems, but no
  reductive groups, Borel subgroups, principal elements `ρ^∨(e^{2πi/h})` or Kostant's cyclic
  elements in that generality, and no Bruhat decomposition; the classical types are done above
  in matrix models, which the exceptional types do not have. In all types, that general position
  of two Borels is the opposition of their flags, and that the Borels through `T'` are the
  stabilisers of the `E'`-stable flags, are used in the statements, not proved. In type `D`, the
  steps `k > n` of the complete flag (the orthogonal duals of the steps `k < n`) are not
  formalised either. The count of the
  quadruples, `|W|²/(h z φ(h))`, is checked as arithmetic in
  `Grothendieck/Folder123Kostant.lean`. The second question (a distinguished conjugacy class of
  quadruples, stable under the outer automorphisms) is not stated either.

## References

* the note on the open problems of the Montpellier notes (`docs/problems/article.tex`), section
  « Abelian varieties and reductive groups », problems p:surf and p:kostant
-/

@[expose] public section


namespace OpenProblems.AbelianVarieties

open Matrix

/-- Kostant's cyclic element for `𝔰𝔩_n` with respect to the diagonal torus and the upper
triangular Borel: `E' = Σ_{i < n-1} cᵢ E_{i,i+1} + c_{n-1} E_{n-1,0}`, the sum of root vectors of
the simple roots and of the lowest root `-θ` with coefficients `cᵢ` (indices from `0`). Its entry
`(i, j)` is `c i` when `j ≡ i + 1 (mod n)` and `0` otherwise. -/
def cyclicElement (n : ℕ) (c : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if (j : ℕ) = ((i : ℕ) + 1) % n then c i else 0

/-- **p:kostant, type `A_{n-1}`** (folder 123, pp. 21–22, letter to Kostant of 22 October 1969).
The letter asks whether, for maximal tori `T, T'` in apposition in Kostant's sense and Borel
subgroups `B ⊇ T`, `B' ⊇ T'`, the Borels `B` and `B'` are always in general position, that is
whether `B ∩ B'` is a maximal torus.

Stated for `G = PGL_n(ℂ)`. Up to conjugacy, `T` is the diagonal torus, `B` the upper triangular
Borel, the stabiliser of the standard flag `F_m = ⟨e₀, …, e_{m-1}⟩`, and `T'` the centraliser of
a cyclic element `E' = cyclicElement n c` with all `cᵢ ≠ 0`. Since `E'ⁿ = (∏ cᵢ) · 1`, `E'` is
regular semisimple, so the Borels through `T'` are the stabilisers of the complete flags
`V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ` stable under `E'`. Two Borels are in general position exactly when their flags
are opposite: `V_k ∩ F_{n-k} = 0` for every `k`, which is the conclusion below (`F_{n-k}` is the
set of vectors whose coordinates of index `≥ n - k` vanish).

Status: proved in type `A`, for every `n`, by
`Grothendieck.Folder123KostantOpposite.kostantOppositeTypeA`
(`Grothendieck/Folder123KostantOpposite.lean`). The note checks type `A₂` by hand (all 36 pairs
opposite). The proof: `E'` is invertible, its inverse a weighted shift of the coordinates up by
one; a nonzero vector of an `E'`-stable `V_k` vanishing on the last `k` coordinates would give,
by `k` applications of that shift, `k + 1` linearly independent vectors of `V_k`. The classical
types `B`, `C`, `D` are `KostantOppositeTypeB`, `KostantOppositeTypeC`, `KostantOppositeTypeD`
below; the exceptional types are open (the note found nothing on the general position). A special
case of the problem, not the problem. -/
@[montpellier "123, 21–22"]
def KostantOppositeTypeA (n : ℕ) : Prop :=
  ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) →
    ∀ V : Fin (n + 1) → Submodule ℂ (Fin n → ℂ), Monotone V →
      (∀ k, Module.finrank ℂ (V k) = k) →
      (∀ k, ∀ v ∈ V k, (cyclicElement n c) *ᵥ v ∈ V k) →
      ∀ k : Fin (n + 1), ∀ v ∈ V k, (∀ j : Fin n, n - (k : ℕ) ≤ (j : ℕ) → v j = 0) → v = 0

/-! ### The classical types `B`, `C`, `D`

The standard matrix models: coordinates `0, …, N - 1`, the bilinear form pairs `e_i` with
`e_{N-1-i}`, the diagonal torus is a maximal torus and the upper triangular matrices of the group
form a Borel subgroup, the stabiliser of the standard (isotropic) flag `F_m = ⟨e₀, …, e_{m-1}⟩`.
The simple root vectors lie on the superdiagonal (and, in type `D`, at the fork of the diagram);
the lowest root vector `X_{-θ}` lies in the bottom left corner. Kostant's cyclic element `E'` is
`Σ aᵢ X_{αᵢ} + a_n X_{-θ}` with all `aᵢ ≠ 0`; its centraliser is a maximal torus `T'` in
apposition to the diagonal one, and the Borels through `T'` are the stabilisers of the
`E'`-stable isotropic flags. -/

/-- The coefficients `a₀, …, a_n` read as a function on `ℕ` (zero beyond `n`). -/
def kostantCoeff (n : ℕ) (a : Fin (n + 1) → ℂ) (i : ℕ) : ℂ :=
  if h : i < n + 1 then a ⟨i, h⟩ else 0

/-- The symmetric form of `ℂ^N` pairing `e_i` with `e_{N-1-i}` (the antidiagonal matrix). The
orthogonal groups `SO_{2n+1}`, `SO_{2n}` are the groups of this form. -/
def antidiagForm (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if (i : ℕ) + j + 1 = N then 1 else 0

/-- The symplectic form of `ℂ^{2n}`: `ω(e_i, e_{2n-1-i}) = 1` for `i < n`, `-1` for `i ≥ n`. -/
def sympForm (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun i j => if (i : ℕ) + j + 1 = 2 * n then (if (i : ℕ) < n then 1 else -1) else 0

/-- The superdiagonal and corner coefficients of Kostant's cyclic element of `𝔰𝔭_{2n}`: the simple
roots `εᵢ - εᵢ₊₁` (`i < n - 1`) have the root vectors `E_{i,i+1} - E_{2n-2-i,2n-1-i}`, the long
simple root `2ε_{n-1}` the root vector `E_{n-1,n}`, the lowest root `-2ε₀` the root vector
`E_{2n-1,0}`. -/
def coeffC (n : ℕ) (a : Fin (n + 1) → ℂ) (i : Fin (2 * n)) : ℂ :=
  if (i : ℕ) < n then kostantCoeff n a i
  else if (i : ℕ) + 1 = 2 * n then kostantCoeff n a n
  else -kostantCoeff n a (2 * n - 2 - i)

/-- Kostant's cyclic element of `𝔰𝔭_{2n}`: `Σ_{i<n} aᵢ X_{αᵢ} + a_n X_{-θ}`. In the ordered basis
`e₀, …, e_{2n-1}` it has exactly the shape of the type `A_{2n-1}` cyclic element:
`cyclicElement (2n) (coeffC n a)`. -/
def cyclicElementC (n : ℕ) (a : Fin (n + 1) → ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  cyclicElement (2 * n) (coeffC n a)

/-- Kostant's cyclic element of `𝔰𝔬_{2n+1}` (type `B_n`, `n ≥ 1`): the simple roots `εᵢ - εᵢ₊₁`
(`i < n - 1`) and `ε_{n-1}` have the root vectors `E_{i,i+1} - E_{2n-1-i,2n-i}` (`i < n`), the
lowest root `-(ε₀ + ε₁)` the root vector `E_{2n-1,0} - E_{2n,1}`; coefficients `a₀, …, a_n`. -/
def cyclicElementB (n : ℕ) (a : Fin (n + 1) → ℂ) :
    Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℂ :=
  fun i j =>
    (if (j : ℕ) = i + 1 then
      (if (i : ℕ) < n then kostantCoeff n a i else -kostantCoeff n a (2 * n - 1 - i)) else 0)
    + (if (i : ℕ) + 2 = 2 * n + 1 ∧ (j : ℕ) = 0 then kostantCoeff n a n else 0)
    - (if (i : ℕ) = 2 * n ∧ (j : ℕ) = 1 then kostantCoeff n a n else 0)

/-- Kostant's cyclic element of `𝔰𝔬_{2n}` (type `D_n`, `n ≥ 3`): the simple roots `εᵢ - εᵢ₊₁`
(`i < n - 1`) have the root vectors `E_{i,i+1} - E_{2n-2-i,2n-1-i}`, the fork root
`ε_{n-2} + ε_{n-1}` the root vector `E_{n-2,n} - E_{n-1,n+1}`, the lowest root `-(ε₀ + ε₁)` the
root vector `E_{2n-2,0} - E_{2n-1,1}`; coefficients `a₀, …, a_{n-2}`, `a_{n-1}` (fork), `a_n`. -/
def cyclicElementD (n : ℕ) (a : Fin (n + 1) → ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun i j =>
    (if (j : ℕ) = i + 1 then
      (if (i : ℕ) + 1 < n then kostantCoeff n a i
        else if n ≤ (i : ℕ) then -kostantCoeff n a (2 * n - 2 - i) else 0) else 0)
    + (if (i : ℕ) + 2 = n ∧ (j : ℕ) = n then kostantCoeff n a (n - 1) else 0)
    - (if (i : ℕ) + 1 = n ∧ (j : ℕ) = n + 1 then kostantCoeff n a (n - 1) else 0)
    + (if (i : ℕ) + 2 = 2 * n ∧ (j : ℕ) = 0 then kostantCoeff n a n else 0)
    - (if (i : ℕ) + 1 = 2 * n ∧ (j : ℕ) = 1 then kostantCoeff n a n else 0)

/-- **p:kostant, type `C_n`** (folder 123, pp. 21–22), for `G = Sp_{2n}(ℂ)`. The Borels through
the centraliser `T'` of `E' = cyclicElementC n a` (all `aᵢ ≠ 0`) are the stabilisers of the
`E'`-stable isotropic flags `V₀ ⊂ ⋯ ⊂ V_n`, extended to complete self-orthogonal flags of
`ℂ^{2n}` by `V_{2n-k} = V_k^⊥`; such a Borel is in general position with respect to the upper
triangular Borel exactly when the complete flag is opposite to the standard one, which is the
conclusion.

Status: proved, by `Grothendieck.Folder123KostantClassical.kostantOppositeTypeC`
(`Grothendieck/Folder123KostantClassical.lean`): in the basis `e₀, …, e_{2n-1}`, `E'` is a type
`A_{2n-1}` cyclic element, so type `A` applies to the whole flag, self-orthogonal or not. -/
def KostantOppositeTypeC (n : ℕ) : Prop :=
  ∀ a : Fin (n + 1) → ℂ, (∀ i, a i ≠ 0) →
    ∀ V : Fin (2 * n + 1) → Submodule ℂ (Fin (2 * n) → ℂ), Monotone V →
      (∀ k, Module.finrank ℂ (V k) = k) →
      (∀ k, ∀ v ∈ V k, (cyclicElementC n a) *ᵥ v ∈ V k) →
      (∀ k, V k.rev = (Matrix.toBilin' (sympForm n)).orthogonal (V k)) →
      ∀ k : Fin (2 * n + 1), ∀ v ∈ V k,
        (∀ j : Fin (2 * n), 2 * n - (k : ℕ) ≤ (j : ℕ) → v j = 0) → v = 0

/-- **p:kostant, type `B_n`** (folder 123, pp. 21–22), for `G = SO_{2n+1}(ℂ)`, `n ≥ 1`: every
`E'`-stable complete self-orthogonal flag of `ℂ^{2n+1}` (`E' = cyclicElementB n a`, all
`aᵢ ≠ 0`) is opposite to the standard one. Here `E'` is not invertible (its kernel is the line of
`a₀ e₀ + a_n e_{2n}`, the zero weight of `T'`).

Status: proved, by `Grothendieck.Folder123KostantClassical.kostantOppositeTypeB`
(`Grothendieck/Folder123KostantClassical.lean`), for every `E'`-stable complete flag. -/
def KostantOppositeTypeB (n : ℕ) : Prop :=
  1 ≤ n → ∀ a : Fin (n + 1) → ℂ, (∀ i, a i ≠ 0) →
    ∀ V : Fin (2 * n + 2) → Submodule ℂ (Fin (2 * n + 1) → ℂ), Monotone V →
      (∀ k, Module.finrank ℂ (V k) = k) →
      (∀ k, ∀ v ∈ V k, (cyclicElementB n a) *ᵥ v ∈ V k) →
      (∀ k, V k.rev = (Matrix.toBilin' (antidiagForm (2 * n + 1))).orthogonal (V k)) →
      ∀ k : Fin (2 * n + 2), ∀ v ∈ V k,
        (∀ j : Fin (2 * n + 1), 2 * n + 1 - (k : ℕ) ≤ (j : ℕ) → v j = 0) → v = 0

/-- **p:kostant, type `D_n`** (folder 123, pp. 21–22), for `G = SO_{2n}(ℂ)`, `n ≥ 3`, the part
that holds for every flag: for an `E'`-stable isotropic flag `V₀ ⊂ ⋯ ⊂ V_{n-1}` of `ℂ^{2n}`
(`E' = cyclicElementD n a`, all `aᵢ ≠ 0`; a Borel of `SO_{2n}` is the stabiliser of such a flag),
`V_k ∩ F_{2n-k} = 0` for every `k < n`. The steps `k > n` of the complete flag `V_{2n-k} = V_k^⊥`
are the orthogonal duals of these. The step `k = n` is not in the statement: `V_{n-1}` lies in two
maximal isotropic subspaces, and a numerical computation (`n = 3, 4, 5`) finds, for each of the
`2^{n-1} n!` Borels through `T'`, exactly one of the two opposite to `F_n`.

Status: proved, by `Grothendieck.Folder123KostantClassical.kostantOppositeTypeD`
(`Grothendieck/Folder123KostantClassical.lean`). Here `E'` has a kernel of dimension 2. -/
def KostantOppositeTypeD (n : ℕ) : Prop :=
  3 ≤ n → ∀ a : Fin (n + 1) → ℂ, (∀ i, a i ≠ 0) →
    ∀ V : Fin n → Submodule ℂ (Fin (2 * n) → ℂ), Monotone V →
      (∀ k, Module.finrank ℂ (V k) = k) →
      (∀ k, ∀ v ∈ V k, (cyclicElementD n a) *ᵥ v ∈ V k) →
      (∀ k, ∀ x ∈ V k, ∀ y ∈ V k, x ⬝ᵥ (antidiagForm (2 * n) *ᵥ y) = 0) →
      ∀ k : Fin n, ∀ v ∈ V k,
        (∀ j : Fin (2 * n), 2 * n - (k : ℕ) ≤ (j : ℕ) → v j = 0) → v = 0

end OpenProblems.AbelianVarieties
