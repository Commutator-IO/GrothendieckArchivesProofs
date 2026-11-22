/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

/-!
# Folder 133: non-constructibility of the affine quotient, not stated

The open row `133-affine-quotient-not-constructible` of the edition's list of findings
(`src/content/findings.ts`), folder 133, pp. 42–43. It cannot be stated faithfully with Mathlib
and the Stacks library; what is missing.

## Not formalised

* `133-affine-quotient-not-constructible`: for smooth group schemes with connected fibres over a
  base of mixed characteristic, the largest affine quotient of the fibres does not vary
  constructibly: an extension `G` of an abelian scheme `A` by `𝐆_a`, non-trivial at a point `y`
  of characteristic `0` and trivial at a specialisation `s` of characteristic `p`, has
  `(G_y)_aff = 1` and `(G_s)_aff ≃ 𝐆_a`. Status: candidate (SGA 3 VI_B § 12 and Brion treat
  `G_aff` over a field or a regular base of dimension `≤ 1`, not its variation in the fibres).
  Missing: extensions of group schemes over a base (exact sequences `0 → 𝐆_a → G → A → 0` in the
  fppf sense, with the kernel of a faithfully flat homomorphism), the largest affine quotient
  `G → G_aff` of a group scheme over a field as a homomorphism of group schemes (Chevalley,
  Rosenlicht; affinisation `Spec Γ(G, O_G)` exists in Mathlib, but not as a quotient group
  scheme), and the identification of `Ext¹(A, 𝐆_a)` with `H¹(A, O_A)` that produces the example.
  Abelian schemes are in the Stacks library (`AlgebraicGeometry.IsAbelianScheme`); the rest would
  be new definitions, and the subject of the page's sentence is an interlinear addition of which
  only « un G » is read.

## References

* A. Grothendieck, folder 133, pp. 42–43 (finding `133-affine-quotient-not-constructible`)
* [SGA 3] VI_B § 12
-/
