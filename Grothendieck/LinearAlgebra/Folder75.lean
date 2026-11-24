/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.StdBasis
import Grothendieck.Attr

/-!
# Folder 75, pages 26–27: the orientation of a direct sum indexed by an unordered set

Pages 26–27 orient a direct sum `⊕_{i ∈ I} E_i` of finite-dimensional real vector spaces indexed
by a finite set `I` without an order: they concatenate oriented bases of the `E_i` along a
numbering of `I`, and stop in the middle of the sign check (« la matrice de passage est de
dét. +1 en tous cas… »). The finding `75-unordered-orientation-of-direct-sum` of the edition
(Commutator-IO/grothendieck-project#247) completes it: exchanging two adjacent blocks of sizes
`d`, `d'` is a permutation of sign `(-1)^{d d'}`, so the orientation obtained depends on the
numbering of `I` only through the indices of odd dimension `I⁻ = {i | d i odd}`, up to even
permutation, whence `ω_{⊕ E_i} ≃ ω_{I⁻} ∧ ⋀_i ω_{E_i}`; for a map of finite sets `p : J → I`,
`ω_J ≃ ω_{I⁻} ∧ ⋀_i ω_{p⁻¹(i)}`, with `I⁻` the indices of the fibres of odd cardinality.

This file proves the sign rule behind both isomorphisms. A numbering of `I` is an equivalence
`e : I ≃ Fin n`; concatenating the blocks `Fin (d i)` in the order of `e` numbers
`Σ i, Fin (d i)` (`concat`), and numbers `J` when the blocks are the fibres of `p`
(`fibreNumbering`). Two numberings `e`, `e'` of `I` induce numberings of `I⁻`
(`oddNumbering`), which differ by a permutation of sign `oddSign d e e'`.

**What the formalisation finds.** Nothing false: the edition's reading holds as stated, and the
determinant identity holds over any commutative ring.

## Main results

* `sign_concat_eq_prod`: the block-exchange sign. The numberings of `Σ i, Fin (d i)` obtained
  from `e` and `e'` differ by a permutation of sign `∏ (-1)^{d i · d j}`, over the pairs
  `(i, j)` that `e` and `e'` order differently (`inversions e e'`).
* `sign_concat`: that sign is `oddSign d e e'`, the sign of the permutation of `I⁻` by which `e`
  and `e'` differ; `oddSign_eq` writes it as `(-1)` to the number of pairs of `I⁻` that `e` and
  `e'` order differently.
* `sign_fibreNumbering`: for `p : J → I`, changing the numbering of `I` and those of the fibres
  changes the numbering of `J` by a permutation of sign `oddSign · ∏_i sign(f_i⁻¹ f'_i)`, with
  `d i = #p⁻¹(i)`; `sign_fibreNumbering_of_eq`, the numbering of `I` alone.
* `det_concatBasis`: over a commutative ring `R`, for bases `b i`, `b' i` of `R`-modules `E i`,
  the determinant of the concatenation of the `b' i` along `e'` in the concatenation of the
  `b i` along `e` is `oddSign d e e' · ∏_i det_{b i}(b' i)` (`⊕ E_i` is `Π i, E i`, `I` being
  finite).
* `orientation_concatBasis`: over an ordered ring (`ℝ` on the page), if each `b' i` has the
  orientation of `b i`, the two concatenations have the same orientation when `oddSign d e e'`
  is `1`, opposite orientations when it is `-1`. So the orientation of `⊕ E_i` built from
  oriented bases and a numbering of `I` depends only on the orientations of the `E_i` and on the
  orientation of `I⁻` (its numbering up to even permutation) that the numbering induces.

## Implementation notes

`numbering r` numbers a finite type by the order of an injection `r` into a linear order; the
concatenation is the numbering by `(i, a) ↦ (e i, a)` in the lexicographic order of
`Fin n × ℕ`. The sign of a change of numbering is computed by its inversions
(`sign_trans_symm`, from `Equiv.Perm.sign_eq_prod_prod_Iio`). Two lemmas missing from Mathlib are
proved here: the determinant of a change of basis of `Π i, E i` preserving the factors
(`det_pi_basis`, through `Matrix.BlockTriangular.det`), and the sign of a permutation of a sigma
type preserving the blocks (`sign_sigmaCongrRight`, deduced from it).

## Not formalised

* The packaging as an isomorphism of `{±1}`-torsors `ω_{⊕ E_i} ≃ ω_{I⁻} ∧ ⋀_i ω_{E_i}`: the
  torsors `ω_{I⁻}`, `ω_{E_i}` and their contracted product are not defined; what is proved is
  the sign rule that makes the map from (orientation of `I⁻`, orientations of the `E_i`) to
  orientations of `⊕ E_i` well defined, with `sign_concat` and `orientation_concatBasis`.
* The version for quadratic modules with orthonormal bases over a connected ring in which `2`
  is invertible: `det_concatBasis` holds over any commutative ring, but orthonormal bases, the
  torsor of their classes and the argument that their changes of basis have determinant `±1`
  are not formalised.

## References

* A. Grothendieck, folder 75, pp. 26–27 (finding `75-unordered-orientation-of-direct-sum`,
  Commutator-IO/grothendieck-project#247)
-/

@[expose] public section

namespace Grothendieck.Folder75

open Equiv Equiv.Perm Finset Module

section Numbering

variable {X : Type*} [Fintype X]

/-- The numbering of `X` by the order of an injection `r` into a linear order. -/
noncomputable def numbering {L : Type*} [LinearOrder L] (r : X ↪ L) : X ≃ Fin (Fintype.card X) :=
  (Equiv.ofInjective r r.injective).trans
    (Fintype.orderIsoFinOfCardEq _ (Set.card_range_of_injective r.injective)).symm.toEquiv

theorem numbering_lt_numbering {L : Type*} [LinearOrder L] (r : X ↪ L) {x y : X} :
    numbering r x < numbering r y ↔ r x < r y := by
  simp [numbering]
  rfl

/-- The pairs `(x, y)` put in the order `x < y` by `f` and in the order `y < x` by `g`. -/
def inversions {L L' : Type*} [LinearOrder L] [LinearOrder L'] (f : X → L) (g : X → L') :
    Finset (X × X) :=
  {p | f p.1 < f p.2 ∧ g p.2 < g p.1}

/-- Two numberings of `X` differ by a permutation of sign `(-1)` to the number of pairs on whose
order they disagree. -/
theorem sign_trans_symm [DecidableEq X] {n : ℕ} (f g : X ≃ Fin n) :
    sign (f.trans g.symm) = (-1) ^ #(inversions f g) := by
  rw [← sign_symm_trans_trans _ g,
    show (g.symm.trans (f.trans g.symm)).trans g = g.symm.trans f by ext; simp,
    sign_eq_prod_prod_Iio, prod_sigma', prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  refine card_nbij' (fun x => (g.symm x.1, g.symm x.2)) (fun p => ⟨g p.1, g p.2⟩) ?_ ?_ ?_ ?_ <;>
    rintro ⟨_, _⟩ h <;> grind [inversions, EmbeddingLike.apply_eq_iff_eq]

end Numbering

section Blocks

variable {I : Type*} [Fintype I] (d : I → ℕ) {n : ℕ}

/-- `(i, a) ↦ (e i, a)`, into the lexicographic order. -/
def lexKey (e : I ≃ Fin n) : (Σ i, Fin (d i)) ↪ Lex (Fin n × ℕ) :=
  ⟨fun x => toLex (e x.1, (x.2 : ℕ)), by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    obtain ⟨rfl, h⟩ : i = j ∧ (a : ℕ) = b := by simpa using h
    exact congrArg _ (Fin.ext h)⟩

/-- The numbering of `Σ i, Fin (d i)` obtained by concatenating the blocks `Fin (d i)` in the
order of the numbering `e` of `I`. -/
noncomputable def concat (e : I ≃ Fin n) :
    (Σ i, Fin (d i)) ≃ Fin (Fintype.card (Σ i, Fin (d i))) :=
  numbering (lexKey d e)

theorem concat_lt_concat (e : I ≃ Fin n) {x y : Σ i, Fin (d i)} :
    concat d e x < concat d e y ↔ e x.1 < e y.1 ∨ x.1 = y.1 ∧ (x.2 : ℕ) < y.2 := by
  simp [concat, numbering_lt_numbering, lexKey, Prod.Lex.toLex_lt_toLex]

theorem mem_inversions_concat (e e' : I ≃ Fin n) {x y : Σ i, Fin (d i)} :
    (x, y) ∈ inversions (concat d e) (concat d e') ↔ (x.1, y.1) ∈ inversions e e' := by
  grind [inversions, concat_lt_concat]

theorem card_inversions_concat (e e' : I ≃ Fin n) :
    #(inversions (concat d e) (concat d e')) = ∑ p ∈ inversions e e', d p.1 * d p.2 := by
  classical
  have : inversions (concat d e) (concat d e') = univ.filter
      fun q : (Σ i, Fin (d i)) × (Σ i, Fin (d i)) => (q.1.1, q.2.1) ∈ inversions e e' := by
    ext ⟨x, y⟩
    simp [mem_inversions_concat]
  let φ : {q : (Σ i, Fin (d i)) × (Σ i, Fin (d i)) // (q.1.1, q.2.1) ∈ inversions e e'} ≃
      Σ p : inversions e e', Fin (d p.1.1) × Fin (d p.1.2) :=
    { toFun q := ⟨⟨(q.1.1.1, q.1.2.1), q.2⟩, (q.1.1.2, q.1.2.2)⟩
      invFun r := ⟨(⟨r.1.1.1, r.2.1⟩, ⟨r.1.1.2, r.2.2⟩), r.1.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [this, ← Fintype.card_subtype, Fintype.card_congr φ, Fintype.card_sigma]
  simpa using sum_coe_sort (inversions e e') fun p => d p.1 * d p.2

theorem neg_one_pow_mul (a b : ℕ) : (-1 : ℤˣ) ^ (a * b) = if Odd a ∧ Odd b then -1 else 1 := by
  simp only [neg_one_pow_eq_ite, ← Nat.not_odd_iff_even]
  grind

/-- The block-exchange sign: reordering the blocks changes the concatenated numbering by a
permutation of sign `∏ (-1) ^ (d i * d j)` over the pairs `(i, j)` that `e` and `e'` order
differently. -/
theorem sign_concat_eq_prod [DecidableEq I] (e e' : I ≃ Fin n) :
    sign ((concat d e).trans (concat d e').symm) =
      ∏ p ∈ inversions e e', (-1 : ℤˣ) ^ (d p.1 * d p.2) := by
  rw [sign_trans_symm, card_inversions_concat, prod_pow_eq_pow_sum]

/-- The numbering of `I⁻ = {i | d i odd}` in the order of the numbering `e` of `I`. -/
noncomputable def oddNumbering (e : I ≃ Fin n) :
    {i // Odd (d i)} ≃ Fin (Fintype.card {i // Odd (d i)}) :=
  numbering ((Function.Embedding.subtype _).trans e.toEmbedding)

/-- The sign of the permutation of `I⁻` by which the numberings `e`, `e'` of `I` differ. -/
noncomputable def oddSign [DecidableEq I] (e e' : I ≃ Fin n) : ℤˣ :=
  sign ((oddNumbering d e).trans (oddNumbering d e').symm)

theorem oddSign_eq [DecidableEq I] (e e' : I ≃ Fin n) :
    oddSign d e e' = (-1) ^ #{p ∈ inversions e e' | Odd (d p.1) ∧ Odd (d p.2)} := by
  rw [oddSign, sign_trans_symm]
  congr 1
  refine card_bij' (fun q _ => (q.1.1, q.2.1)) (fun p hp => (⟨p.1, (mem_filter.1 hp).2.1⟩,
    ⟨p.2, (mem_filter.1 hp).2.2⟩)) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  all_goals rintro ⟨x, y⟩ h
  all_goals simp only [inversions, mem_filter, mem_univ, true_and, oddNumbering,
    numbering_lt_numbering] at h ⊢
  exacts [⟨h, x.2, y.2⟩, h.1]

/-- **Pages 26–27, the sign check.** Concatenating blocks of sizes `d i` along two numberings
`e`, `e'` of `I` gives two numberings of `Σ i, Fin (d i)` that differ by a permutation of the
same sign as the permutation of `I⁻ = {i | d i odd}` by which `e` and `e'` differ. -/
@[montpellier "75, 26–27"]
theorem sign_concat [DecidableEq I] (e e' : I ≃ Fin n) :
    sign ((concat d e).trans (concat d e').symm) = oddSign d e e' := by
  rw [sign_concat_eq_prod, oddSign_eq, prod_congr rfl fun p _ => neg_one_pow_mul _ _, prod_ite,
    prod_const, prod_const_one, mul_one]

end Blocks

section Determinant

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]
  {E : I → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

/-- The determinant of a change of basis of `Π i, E i` that preserves each factor is the
product of the determinants on the factors. -/
theorem det_pi_basis {ι : I → Type*} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b b' : ∀ i, Basis (ι i) R (E i)) :
    (Pi.basis b).det (Pi.basis b') = ∏ i, (b i).det (b' i) := by
  let : LinearOrder I := LinearOrder.lift' _ (Fintype.equivFin I).injective
  have hM : (Pi.basis b).toMatrix (Pi.basis b') =
      Matrix.blockDiagonal' fun i => (b i).toMatrix (b' i) := by
    ext ⟨i, x⟩ ⟨j, y⟩
    obtain rfl | h := eq_or_ne i j <;>
      simp [Basis.toMatrix_apply, Matrix.blockDiagonal'_apply_ne, *]
  rw [Basis.det_apply, hM, (Matrix.blockTriangular_blockDiagonal' _).det]
  refine (prod_subset (subset_univ _) fun i _ hi => ?_).trans (prod_congr rfl fun i _ => ?_)
  · have : IsEmpty {x : Σ i, ι i // x.1 = i} := ⟨fun x => hi (mem_image.2 ⟨x.1, mem_univ _, x.2⟩)⟩
    exact Matrix.det_isEmpty
  · rw [Basis.det_apply, ← Matrix.det_submatrix_equiv_self (sigmaSubtype i).symm]
    congr 1
    ext x y
    simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, sigmaSubtype]

variable (d : I → ℕ) {n : ℕ}

/-- The basis of `Π i, E i` obtained by concatenating bases `b i` of the `E i` in the order
of a numbering `e` of `I`. -/
noncomputable def concatBasis (e : I ≃ Fin n) (b : ∀ i, Basis (Fin (d i)) R (E i)) :
    Basis (Fin (Fintype.card (Σ i, Fin (d i)))) R (∀ i, E i) :=
  (Pi.basis b).reindex (concat d e)

/-- **Pages 26–27, the determinant of the change of basis.** Between the concatenations of
bases `b i`, `b' i` along numberings `e`, `e'` of `I`, the determinant is the sign of the
permutation of `I⁻` by which `e` and `e'` differ, times the determinants on the blocks. -/
@[montpellier "75, 26–27"]
theorem det_concatBasis (e e' : I ≃ Fin n) (b b' : ∀ i, Basis (Fin (d i)) R (E i)) :
    (concatBasis d e b).det (concatBasis d e' b') =
      (oddSign d e e' : ℤ) * ∏ i, (b i).det (b' i) := by
  rw [concatBasis, Basis.det_reindex, concatBasis, Basis.coe_reindex, ← sign_concat,
    ← det_pi_basis, Function.comp_assoc, ← coe_trans, AlternatingMap.map_perm, Units.smul_def,
    zsmul_eq_mul]

end Determinant

section Orientation

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R] {E : I → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  (d : I → ℕ) {n : ℕ}

/-- **Pages 26–27, the orientation of `⊕ E_i`.** For bases `b i`, `b' i` of the same
orientation, the concatenations along numberings `e`, `e'` of `I` give the same orientation if
`e` and `e'` differ by an even permutation of `I⁻`, opposite orientations otherwise. -/
@[montpellier "75, 26–27"]
theorem orientation_concatBasis (e e' : I ≃ Fin n) (b b' : ∀ i, Basis (Fin (d i)) R (E i))
    (h : ∀ i, (b i).orientation = (b' i).orientation) :
    (concatBasis d e' b').orientation = if oddSign d e e' = 1 then (concatBasis d e b).orientation
      else -(concatBasis d e b).orientation := by
  have hpos : 0 < ∏ i, (b i).det (b' i) :=
    prod_pos fun i _ => (Basis.orientation_eq_iff_det_pos _ _).1 (h i)
  split_ifs with hs
  · rw [eq_comm, Basis.orientation_eq_iff_det_pos, det_concatBasis, hs]
    simpa using hpos
  · rw [← Basis.orientation_ne_iff_eq_neg, ne_comm, Ne, Basis.orientation_eq_iff_det_pos,
      det_concatBasis, Int.units_ne_iff_eq_neg.1 hs]
    simpa using hpos.le

end Orientation

section Fibres

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (p : J → I) {n : ℕ}

/-- The sign of a permutation `σ` is the determinant of a basis `c` permuted by `σ`, with respect
to `c`. -/
theorem sign_eq_det_comp {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M] [Module ℤ M]
    (c : Basis κ ℤ M) (σ : Perm κ) : (sign σ : ℤ) = c.det (c ∘ σ) := by
  simp [AlternatingMap.map_perm, Units.smul_def, Basis.det_self]

/-- The sign of a permutation of `Σ i, β i` preserving each block is the product of the signs
on the blocks. -/
theorem sign_sigmaCongrRight {β : I → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (τ : ∀ i, Perm (β i)) : sign (Equiv.sigmaCongrRight τ) = ∏ i, sign (τ i) := by
  let b i := Pi.basisFun ℤ (β i)
  have : ⇑(Pi.basis b) ∘ Equiv.sigmaCongrRight τ =
      Pi.basis fun i => (b i).reindex (τ i).symm := by
    ext ⟨i, x⟩ : 1
    simp
  refine Units.ext ?_
  rw [Units.coe_prod, sign_eq_det_comp (Pi.basis b), this, det_pi_basis]
  exact prod_congr rfl fun i _ => by rw [sign_eq_det_comp (b i)]; simp

/-- The numbering of `J` obtained by concatenating numberings `f i` of the fibres `p⁻¹(i)` in
the order of a numbering `e` of `I`. -/
noncomputable def fibreNumbering (f : ∀ i, {j // p j = i} ≃ Fin (Fintype.card {j // p j = i}))
    (e : I ≃ Fin n) : J ≃ Fin (Fintype.card (Σ i, Fin (Fintype.card {j // p j = i}))) :=
  (sigmaFiberEquiv p).symm.trans ((Equiv.sigmaCongrRight f).trans (concat _ e))

/-- **Pages 26–27, the case of a map of finite sets: `ω_J ≃ ω_{I⁻} ∧ ⋀ ω_{p⁻¹(i)}`.**
Changing the numbering `e` of `I` into `e'` and the numberings `f i` of the fibres into `f' i`
changes the numbering of `J` by a permutation whose sign is the sign by which `e` and `e'`
differ on `I⁻`, the indices of the fibres of odd cardinality, times the signs by which the
numberings of the fibres differ. -/
@[montpellier "75, 26–27"]
theorem sign_fibreNumbering (f f' : ∀ i, {j // p j = i} ≃ Fin (Fintype.card {j // p j = i}))
    (e e' : I ≃ Fin n) :
    sign ((fibreNumbering p f e).trans (fibreNumbering p f' e').symm) =
      oddSign (fun i => Fintype.card {j // p j = i}) e e' *
        ∏ i, sign ((f i).trans (f' i).symm) := by
  have : (fibreNumbering p f e).trans (fibreNumbering p f' e').symm =
      ((sigmaFiberEquiv p).symm.trans
        ((Equiv.sigmaCongrRight fun i => (f i).trans (f' i).symm).trans
          (((Equiv.sigmaCongrRight f').trans ((concat _ e).trans (concat _ e').symm)).trans
            (Equiv.sigmaCongrRight f').symm))).trans (sigmaFiberEquiv p).symm.symm := by
    ext
    simp [fibreNumbering]
  rw [this, sign_trans_trans_symm, sign_trans, sign_trans_trans_symm, sign_concat,
    sign_sigmaCongrRight]

/-- **Pages 26–27, the numbering of `I` alone.** With the numberings of the fibres fixed, a
change of the numbering of `I` changes that of `J` by a permutation of the sign by which the two
numberings of `I⁻` differ. -/
@[montpellier "75, 26–27"]
theorem sign_fibreNumbering_of_eq (f : ∀ i, {j // p j = i} ≃ Fin (Fintype.card {j // p j = i}))
    (e e' : I ≃ Fin n) :
    sign ((fibreNumbering p f e).trans (fibreNumbering p f e').symm) =
      oddSign (fun i => Fintype.card {j // p j = i}) e e' := by
  simp [sign_fibreNumbering]

end Fibres

end Grothendieck.Folder75

