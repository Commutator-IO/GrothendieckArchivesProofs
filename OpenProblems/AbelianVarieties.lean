module

public import Mathlib
import Grothendieck.Attr

@[expose] public section

/-!
# Abelian varieties and reductive groups: the open problems, stated as propositions

Section « Abelian varieties and reductive groups » of the note on the open problems of the
Montpellier notes (`docs/problems/article.tex`): problems p:surf and p:kostant. Nothing here is
proved; a `def … : Prop` asserts nothing.

## Stated

* `KostantOppositeTypeA` (p:kostant): the question of general position, for the groups of type
  `A_{n-1}` (`G = PGL_n(ℂ)`) only. A special case. Proved for every `n`:
  `Grothendieck.Folder123KostantOpposite.kostantOppositeTypeA`
  (`Grothendieck/Folder123KostantOpposite.lean`).

## Not stated, and what is missing

* p:surf (is `Pic^δ_{A/S}` a trivial torsor under the dual `B` when `A/S` is an abelian scheme of
  relative dimension 2 and `χ(δ)` is even?). Stacks has abelian varieties over a field
  (`IsAbelianVariety`) and abelian schemes (`IsAbelianScheme`), but not the dual abelian scheme
  `Pic⁰_{A/S}`, the Néron–Severi sheaf `NS_{A/S}`, the torsors `Pic^δ_{A/S}`, or the Euler
  characteristic `χ(δ)` of a class; the Poonen–Stoll class `c_δ ∈ H¹(k, B)` needs all of them.
  Over a field the question reads: for an abelian surface `A/k` and a Galois-invariant class `δ`
  of `NS(A_{k̄})` with `χ(δ)` even, is `δ` the class of a line bundle defined over `k`? Even that
  needs `NS` of a base change and its Galois action.
* p:kostant in general (any simple adjoint group): Mathlib has Lie algebras, Cartan subalgebras
  and root systems, but no reductive groups, Borel subgroups, principal elements `ρ^∨(e^{2πi/h})`
  or Kostant's cyclic elements in that generality, and no Bruhat decomposition. The count of the
  quadruples, `|W|²/(h z φ(h))`, is checked as arithmetic in
  `Grothendieck/Folder123Kostant.lean`. The second question (a distinguished conjugacy class of
  quadruples, stable under the outer automorphisms) is not stated either.
-/

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
by `k` applications of that shift, `k + 1` linearly independent vectors of `V_k`. The question is
open for the other types (the note found nothing on the general position). A special case of the
problem, not the problem. -/
@[montpellier "123, 21–22"]
def KostantOppositeTypeA (n : ℕ) : Prop :=
  ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) →
    ∀ V : Fin (n + 1) → Submodule ℂ (Fin n → ℂ), Monotone V →
      (∀ k, Module.finrank ℂ (V k) = k) →
      (∀ k, ∀ v ∈ V k, (cyclicElement n c) *ᵥ v ∈ V k) →
      ∀ k : Fin (n + 1), ∀ v ∈ V k, (∀ j : Fin n, n - (k : ℕ) ≤ (j : ℕ) → v j = 0) → v = 0

end OpenProblems.AbelianVarieties
