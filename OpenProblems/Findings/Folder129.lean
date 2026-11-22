/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

/-!
# Folder 129: vanishing of `𝓔xt²`, not stated

The open row `129-ext2-vanishing-p-odd` of the edition's list of findings
(`src/content/findings.ts`), folder 129, p. 95. It is not stated; why. It is the same statement as
p:ext2 of the note on the open problems, also not stated in `OpenProblems/EtaleCohomology.lean`.

* `129-ext2-vanishing-p-odd`: `𝓔xt²_ℤ(G, M) = 0` for every finite locally free commutative group
  scheme `G` and quasi-coherent `M` as soon as `2` is invertible. Status: doubtful. The word
  carrying the hypothesis (« inv. ») is an uncertain reading and the page gives no proof; read
  this way the NB is in tension with Illusie (2023), who places the obstruction to deforming a
  `BT_n` in `Ext²_ℤ(G₀, t_{G₀} ⊗ J)` and calls a direct proof of its vanishing out of reach; the
  row proposes computing `𝓔xt²_ℤ(α_p, 𝐆_a)` over a perfect field of odd characteristic. Missing:
  the sheaf `𝓔xt²` on the big fppf site (the sheafification of the `Ext²` of the restrictions to
  the sites over each object), the restriction of abelian sheaves to those sites, and the
  quasi-coherent module `M` as an abelian fppf sheaf `T ↦ Γ(T, M_T)`. The Stacks library has the
  big fppf site (`AlgebraicGeometry.BigFppfSite`, Stacks 021R) and the abelian presheaf of points
  of a commutative group scheme on it, and Mathlib has `Ext` in abelian categories, but not that
  package; a global `Ext²` over the base would be a different statement.
-/
