/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Order.Lattice
import Grothendieck.Attr

/-!
# Folder 161-2, page 48: the join of two subtopoi glued along opens, in a distributive lattice

The finding `161-2-definite-characteristic-join-of-subtopoi` (`src/content/findings.ts`) reads in
the brouillon of page 48 a gluing lemma for subtopoi `V, W` of a topos `B`: the join `V ⊔ W` is
obtained by gluing `V` and `W` along opens `Z' ⊆ V`, `Z'' ⊆ W`, in Grothendieck's form
`V = Z' ∪ (Z'' ∩ V)` and `W = Z'' ∪ (Z' ∩ W)`. Written out (issue
Commutator-IO/grothendieck-project#185), the lemma is a statement about the lattice of subtopoi
alone: it is a co-Heyting algebra, so distributive, the open subtopos `o(U)` of a subobject
`U ⊆ 1` is an element of it, and `o(U') ⊔ o(U'') = o(U' ∪ U'')`. This file proves that
order-theoretic core, in any distributive lattice, for any two elements `o'`, `o''` standing for
the opens.

**What the formalisation finds.** Nothing false. Openness plays no part: the equivalence of the
two forms of the condition, and Grothendieck's form of the gluing, hold for any two elements
`o'`, `o''` of a distributive lattice. Distributivity is used only where the trace on `o'` of the
join `V ⊔ W` is split into the traces of `V` and `W`, and where `V = V ⊓ (o' ⊔ o'')` is split
into `Z'` and the trace of `V` on `o''`.

## Main results

With `Z = V ⊔ W`, `Z' = V ⊓ o'` and `Z'' = W ⊓ o''`:

* `recollement_iff`: the two forms of the condition are equivalent:
  (ii) `Z` is the union of its traces `Z ⊓ o'` and `Z ⊓ o''`, with `Z ⊓ o' ≤ V` and
  `Z ⊓ o'' ≤ W`; (iii) `W ⊓ o' ≤ V`, `V ⊓ o'' ≤ W`, `V ≤ o' ⊔ o''` and `W ≤ o' ⊔ o''`;
* `inf_left_eq_of_recollement`, `inf_right_eq_of_recollement`: under (ii), the two opens of `Z`
  are `Z ⊓ o' = Z'` and `Z ⊓ o'' = Z''`;
* `recollement_left`, `recollement_right`: Grothendieck's form, `V = Z' ⊔ (Z'' ⊓ V)` and
  `W = Z'' ⊔ (Z' ⊓ W)`, each from the two conditions of (iii) that concern it;
* `recollement`: the page-48 statement, (ii) implies Grothendieck's form.

## Implementation notes

The lemma is stated for a `DistribLattice`; a co-Heyting algebra (Mathlib's `CoheytingAlgebra`,
an `Order.Coframe` in particular) is one, which is the case of the lattice of subtopoi. The
elements `o'`, `o''` are arbitrary: « `Z ⊓ o'` is an open of `Z` » is not part of the statement,
which needs only the order. The names are French, as in the rest of the folder's files.

## Not formalised

The instance of the lemma on subtopoi. Mathlib's `CategoryTheory.GrothendieckTopology C` is a
complete lattice, and the subtopoi of `Sheaf J (Type u)` are in order-reversing bijection with the
topologies finer than `J` (`LeanPool.ToposTheoreticBridges.subtoposOrderIso`, where `Subtopos` is
only a partial order), but the libraries lack:

* distributivity of that lattice: the topologies on a site form a frame (the subtopoi a coframe,
  Johnstone §A4.5), which is neither in Mathlib nor in Stacks, so there is no
  `DistribLattice (GrothendieckTopology C)` to apply the lemma to;
* the open subtopos `o(U)` of a subterminal object `U` as a topology (Stacks has the predicate
  `IsOpenSubtopos` on a class of sheaves, tag 08LX, not the map `U ↦ o(U)`), and the equality
  `o(U') ⊔ o(U'') = o(U' ∪ U'')`, which needs joins of subtopoi;
* the gluing itself: that a subtopos is recovered from its restrictions to an open cover, i.e.
  the factorisation through `V ⊔ W` that makes « obtained by gluing » a construction.

## References

* A. Grothendieck, Folder 161-2, pp. 47–49, *Algèbre universelle* (finding
  `161-2-definite-characteristic-join-of-subtopoi`)
* P. T. Johnstone, *Sketches of an Elephant*, §A4.5 (open subtopoi, the coframe of subtopoi)
-/

@[expose] public section

namespace Grothendieck.Folder161_2

variable {α : Type*} [DistribLattice α] {V W o' o'' : α}

/-- **Page 48, the two forms of the gluing condition.** For `V, W` in a distributive lattice and
`Z = V ⊔ W`: `Z` is the union of its traces on `o'` and `o''`, lying in `V` and in `W`
respectively, iff `W ⊓ o' ≤ V`, `V ⊓ o'' ≤ W`, and `V`, `W` both lie in `o' ⊔ o''`. -/
@[montpellier "161-2, 48"]
theorem recollement_iff :
    ((V ⊔ W) ⊓ o' ⊔ (V ⊔ W) ⊓ o'' = V ⊔ W ∧ (V ⊔ W) ⊓ o' ≤ V ∧ (V ⊔ W) ⊓ o'' ≤ W) ↔
      W ⊓ o' ≤ V ∧ V ⊓ o'' ≤ W ∧ V ≤ o' ⊔ o'' ∧ W ≤ o' ⊔ o'' := by
  refine ⟨fun ⟨h, h', h''⟩ => ?_, fun ⟨h₁, h₂, h₃, h₄⟩ => ?_⟩
  · have h₀ := h.ge.trans (sup_le_sup inf_le_right inf_le_right)
    exact ⟨(inf_le_inf_right _ le_sup_right).trans h', (inf_le_inf_right _ le_sup_left).trans h'',
      le_sup_left.trans h₀, le_sup_right.trans h₀⟩
  · exact ⟨(inf_sup_left _ _ _).symm.trans (inf_eq_left.2 (sup_le h₃ h₄)),
      (inf_sup_right _ _ _).le.trans (sup_le inf_le_left h₁),
      (inf_sup_right _ _ _).le.trans (sup_le h₂ inf_le_left)⟩

/-- Under the gluing condition, the open `(V ⊔ W) ⊓ o'` of the join is `Z' = V ⊓ o'`. -/
@[montpellier "161-2, 48"]
theorem inf_left_eq_of_recollement (h : (V ⊔ W) ⊓ o' ≤ V) : (V ⊔ W) ⊓ o' = V ⊓ o' :=
  le_antisymm (le_inf h inf_le_right) (inf_le_inf_right _ le_sup_left)

/-- Under the gluing condition, the open `(V ⊔ W) ⊓ o''` of the join is `Z'' = W ⊓ o''`. -/
@[montpellier "161-2, 48"]
theorem inf_right_eq_of_recollement (h : (V ⊔ W) ⊓ o'' ≤ W) : (V ⊔ W) ⊓ o'' = W ⊓ o'' :=
  sup_comm V W ▸ inf_left_eq_of_recollement (sup_comm V W ▸ h)

/-- **Page 48, Grothendieck's form, first half.** If `V ⊓ o'' ≤ W` and `V ≤ o' ⊔ o''`, then
`V = Z' ⊔ (Z'' ⊓ V)` with `Z' = V ⊓ o'` and `Z'' = W ⊓ o''`. -/
@[montpellier "161-2, 48"]
theorem recollement_left (h₂ : V ⊓ o'' ≤ W) (h₃ : V ≤ o' ⊔ o'') :
    V = V ⊓ o' ⊔ W ⊓ o'' ⊓ V :=
  le_antisymm ((le_inf le_rfl h₃).trans ((inf_sup_left _ _ _).le.trans
    (sup_le_sup_left (le_inf (le_inf h₂ inf_le_right) inf_le_left) _)))
    (sup_le inf_le_left inf_le_right)

/-- **Page 48, Grothendieck's form, second half.** If `W ⊓ o' ≤ V` and `W ≤ o' ⊔ o''`, then
`W = Z'' ⊔ (Z' ⊓ W)` with `Z' = V ⊓ o'` and `Z'' = W ⊓ o''`. -/
@[montpellier "161-2, 48"]
theorem recollement_right (h₁ : W ⊓ o' ≤ V) (h₄ : W ≤ o' ⊔ o'') :
    W = W ⊓ o'' ⊔ V ⊓ o' ⊓ W :=
  recollement_left h₁ (sup_comm o' o'' ▸ h₄)

/-- **Page 48, the gluing lemma.** If `Z = V ⊔ W` is the union of its traces on `o'` and `o''`,
lying in `V` and in `W` respectively, then `V = Z' ⊔ (Z'' ⊓ V)` and `W = Z'' ⊔ (Z' ⊓ W)`, with
`Z' = V ⊓ o'` and `Z'' = W ⊓ o''`. -/
@[montpellier "161-2, 48"]
theorem recollement
    (h : (V ⊔ W) ⊓ o' ⊔ (V ⊔ W) ⊓ o'' = V ⊔ W ∧ (V ⊔ W) ⊓ o' ≤ V ∧ (V ⊔ W) ⊓ o'' ≤ W) :
    V = V ⊓ o' ⊔ W ⊓ o'' ⊓ V ∧ W = W ⊓ o'' ⊔ V ⊓ o' ⊓ W :=
  have ⟨h₁, h₂, h₃, h₄⟩ := recollement_iff.1 h
  ⟨recollement_left h₂ h₃, recollement_right h₁ h₄⟩

end Grothendieck.Folder161_2
