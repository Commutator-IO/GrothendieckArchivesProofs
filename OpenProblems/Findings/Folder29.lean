/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

/-!
# Folder 29: ramification domains and torsors under infinite groups, not stated

Two open rows of the edition's list of findings (`src/content/findings.ts`) for folder 29
(*Groupe fondamental*). Neither can be stated faithfully with Mathlib and the Stacks library; for
each, what is missing. The neighbouring problem p:domram (folder 29, p. 197) is in
`OpenProblems/TopoiStacks.lean`.

* `29-ramification-domain-axioms` (pp. 190–193): a « domaine de ramification » is a stack of
  multigaloisian categories over `Ét(S)` with a continuous geometric realisation `r` into relative
  schemes, subject to axioms R1–R4, and given R1, R3, R4, axiom R2 (direct subobjects of `X`
  correspond to open-and-closed parts of `r(X)`) is equivalent to `r` faithful. Status:
  candidate (nothing found; the closest is Lieblich–Olsson 2010, Appendix A). Missing:
  multigaloisian categories, stacks of categories over the small étale site with a realisation
  functor into relative schemes, and the axioms themselves. Mathlib has Galois categories
  without fibre functor (`PreGaloisCategory`) and Stacks has stacks over a site, but the setting
  would be new definitions, and axiom R4 is partly illegible and page 193 is struck, so the
  statement being compared is itself uncertain.
* `29-h1-five-classes-infinite-group` (pp. 170–171): for a discrete, possibly infinite group
  `G`, the comparison of `H¹_C(S, G) = lim_{T/S} H¹(π₀(K_{T/S}), G)` across five classes `C` of
  covering families, with four comparison statements (in general, over a Dedekind ring, over a
  complete discrete valuation ring with algebraically closed residue field, over a complete
  local ring). Status: unsearched. Missing: `H¹_C` is defined through the groupoid of connected
  components `π₀(K_{T/S})` of the Čech groupoid of a covering and its non-abelian cohomology,
  which neither library has; the classes « finite principal » and « finite étale principal »
  are the folder's and have no counterpart. Torsors trivialised by a covering of a given class
  (`AlgebraicGeometry.IsTorsorFor` of the Stacks library, for a precoverage) agree with `H¹_C`
  only when descent is effective, which for infinite `G` is the content of the row; stating the
  comparisons with them would change the statement.
-/
