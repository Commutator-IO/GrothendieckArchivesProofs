/-!
# Folder FG_IL_5_SGA7_4: depth and local acyclicity, not stated

The open row `FG_IL_5_SGA7_4-depth-local-acyclicity` of the edition's list of findings
(`src/content/findings.ts`), folder FG_IL_5_SGA7_4, p. 28 (with pp. 21–27 for 5.1–5.7 a)). It
cannot be stated faithfully with Mathlib and the Stacks library; what is missing.

* `FG_IL_5_SGA7_4-depth-local-acyclicity`: the conjecture of Remarque 5.7 b), that a flat
  morphism `Spec B → Spec A` of noetherian strictly local schemes whose special fibre has, after
  every finite residue extension, a singular locus of dimension `≤ d` is locally
  `(m − d − 1)`-acyclic for primes `≠ p`, `m` the geometric depth of `B`, and locally
  1-aspherical when `m − d ≥ 2`. Status: candidate (not found proved or refuted; its two inputs,
  SGA 2 XIV 6.3 and Illusie 2003 over a trait, are in print). Missing: local `n`-acyclicity (the
  vanishing of the vanishing-cycle cohomology `Φ^i` for `i ≤ n − 1`), local 1-asphericity, and
  the geometric depth (« prof géom », which the page uses for `B` where Cor. 5.3 uses the special
  fibre). The Stacks library has local acyclicity in full (`AlgebraicGeometry.IsLocallyAcyclicAt`,
  Stacks 0GJP: an isomorphism of the vanishing-cycle fibre map in the derived category), from
  which a truncated variant would have to be defined; neither library has the singular locus of
  a fibre after residue extensions as a scheme with a dimension.
-/
