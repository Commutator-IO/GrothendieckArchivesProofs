module

/-!
# Algebraic cycles: the open problem p:lef, not stated

Section « Algebraic cycles » of the note on the open problems of the Montpellier notes
(`docs/problems/article.tex`) holds one problem, p:lef (folder 16, p. 49, letter of January 1967):
whether the reduction of the Lefschetz standard conjecture
`C(X) ⟺ C(Y) + A'⁰(X × X) + A''⁰(X × X)` holds as stated, that is, whether the critical
Lefschetz condition `A⁰(Y_T)` on a hyperplane section `Y_T` of `T = X × X` can be dropped from
`C(Y) + A'⁰(X × X) + A''⁰(X × X) + A⁰(Y_T) ⟹ C(X)`. Status: open; the equivalence
`C(X) ⟺ C(Y) + A⁰(X × X)` is Kleiman's (1968, Th. 2.13).

Not stated, because a faithful statement needs, on top of a Weil cohomology theory: smooth
hyperplane sections `φ : Y ↪ X` of a smooth projective variety (zero loci of sections of a very
ample line bundle), the Lefschetz operator `L` as cup product with the class of `Y`, the maps
`φ^*` and `φ_*` on cohomology, the subspaces of algebraic classes (images of the cycle class map),
and the Lefschetz standard conjecture `C(X)` itself, which asks that the inverse of
`L^{n-i}` be given by the action of an algebraic class of `H(X × X)` through the Künneth
decomposition. The Stacks library has Weil cohomology theories
(`Stacks.WeilCohomology.WeilCohomologyTheory`) with cycle classes, Künneth and Poincaré duality,
so the missing part is this layer of definitions, not the theory; writing it without a local
build to check it against that library's API was not attempted. A statement in abstract linear
algebra (cohomology groups as modules, algebraic classes as submodules, weak and hard Lefschetz
as hypotheses) would not be faithful: the question is whether the geometry of `Y_T` is needed,
which an abstract setting cannot see. The two linear-algebra halves of the reconstruction are proved
in `Grothendieck/Folder16.lean` (`split_even`, `split_odd`, `split_odd_circular`).
-/
