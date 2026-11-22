/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

/-!
# Folder 136: automorphisms of divided-power de Rham algebras, not stated

The open row `136-automorphism-group-scheme` of the edition's list of findings
(`src/content/findings.ts`), folder 136, pp. 161–179, 189–199. It cannot be stated faithfully
with Mathlib and the Stacks library; what is missing.

* `136-automorphism-group-scheme`: the simplicial-ring homomorphisms between the divided-power de
  Rham algebras `𝒜(S, S⁺, t)_*` (no grading, filtration or divided powers assumed) are classified
  by data `(φ₀, A'₁, (B'_i))` subject to three conditions, the third `(2B'_i)J' = 0`; hence the
  automorphism functor of the completed algebra over `k{T}` is an affine group scheme over `ℤ`,
  `𝐆_m ⋉ (unipotent)` with factors killed by `2`, and when `2` is invertible every automorphism
  preserves the exterior grading and acts on cohomology through `𝐆_m`. Status: candidate (nothing
  found on endomorphisms of simplicial polynomial forms). Missing: the simplicial algebras
  `𝒜(S, S⁺, t)_*` themselves and their completion over `k{T}`; Mathlib has simplicial objects
  and divided-power structures, and the Stacks library's crystalline de Rham complexes (07LG)
  concern a different object, so they would have to be built by hand, and the data
  `(φ₀, A'₁, (B'_i))` are defined by coefficients on the folder's pages; the exponent by which
  automorphisms act on `H^i` is not fixed (the page's phrase is largely illegible).
-/
