/-!
# Folder 16: the weak variants of the Lefschetz conditions, not stated

The open row `16-weak-variants-imply-strong` of the edition's list of findings
(`src/content/findings.ts`), folder 16, p. 49 (letter to Coates, January 1967). It cannot be
stated faithfully with Mathlib and the Stacks library; what is missing.

* `16-weak-variants-imply-strong`: the critical-dimension conditions `A'⁰(T)` (a class of
  `H^i(T)`, `2i = n − 1` or `n − 2`, whose restriction to a hyperplane section `Y` is algebraic
  is algebraic) and `A''⁰(T)` (every algebraic class of `H^{i+2}(T)` is the Gysin image of an
  algebraic class of `H^i(Y)`) together imply `A⁰(T)`, the critical-dimension Lefschetz
  condition, so that `C(X)` is equivalent to `C(Y) + A'⁰(X × X) + A''⁰(X × X)`. Status: the
  equivalence with `C(Y) + A⁰(X × X)` and the descent along hyperplane sections are Kleiman 1968,
  Th. 2.13; the split of `A⁰` into `A'⁰` and `A''⁰` was not found (André 2004, ch. 5, still to
  read). Missing: the axiomatic Weil cohomology of the Stacks library
  (`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory`, Stacks 0FGV) has cycle classes, cup
  product and Gysin maps, but no hyperplane section `φ : Y → T` of a projective variety with its
  pullback and Gysin map in cohomology, no Lefschetz operator `L_T = φ_* φ^*` and no `Λ`; the
  conditions `A⁰`, `A'⁰`, `A''⁰`, `C` are about those operators, and the folder's letters use
  `A`, `C`, `D` in senses that do not match the published labels, so each would have to be
  rebuilt from the leaf.
-/
