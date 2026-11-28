/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

/-!
# Moduli of curves and Galois actions: the open problems, not stated

Section « Moduli of curves and Galois actions » of the note on the open problems of the
Montpellier notes (`docs/problems/article.tex`): problems p:gal and p:nc, and the conjecture of
folder 143 on `Out°_lac`. None can be stated faithfully with Mathlib and the Stacks library; for
each, what is missing.

## Not formalised

* p:gal (folder 142, pp. 94–95, 98–101, *Action de Galois sur Teichmüller*, [from 1978]; finding
  `142-galois-image-conditions-single-curve`): for one curve `X` over a field `K`, the page lists
  necessary conditions for a vertex-fixing automorphism `Θ` of the profinite fundamental groupoid
  `Π̂₁(X, I)` to come from `Gal(K̄/K)`: lifting to `Π̂₁(X′, I′)` for every finite étale cover `X′`
  defined over `K`; stability of the kernels of `π̂₁(X′, x′) → π̂₁(Y, f(x′))` for every
  `K`-morphism `f`; compatibility along morphisms between covers; and the loop (inertia)
  condition at the cusps with a single multiplier. It conjectures that the first two are
  « suffisamment draconiennes » for `Θ` to come from `Gal(K̄/K)` when `X` is anabelian
  (hyperbolic) and `K` is of finite type over `ℚ`. Status: open (Pop's theorem and its tripod
  variants need bases of dimension greater than one). Missing: the profinite étale fundamental
  groupoid on several base points with its functoriality in finite étale covers, hyperbolic
  curves, cusps and their inertia, and the outer Galois action. Mathlib has Galois categories and
  fibre functors, and Stacks has pieces of the étale fundamental group, but not this groupoid
  with its Galois action.
* p:nc (folder 147, pp. 148–151, *Structure à l'infini des `M_{g,ν}`*, winter 1982–1983): is the
  deleted tubular neighbourhood of a normal crossings divisor `Θ` in a smooth complex analytic
  space (or orbifold) the homotopy colimit of the deleted neighbourhoods of the strata of its
  unfolding, so that its fundamental groupoid is the amalgamated sum of the groupoids of the
  torus bundles over the strata of codimension 1 and 2? Status: open (not found in this form;
  the two-level principle for the discrete tower is Hatcher, Lochak and Schneps). Missing:
  complex analytic spaces and orbifolds, normal crossings divisors and their unfolding, tubular
  neighbourhoods, homotopy colimits of spaces, and fundamental groupoids of stratified spaces.
* folder 143, pp. 28–30 (finding `143-moduli-outlac-conjecture`): for every `(g, ν)` with
  `2g − 2 + ν > 0`, is the monodromy map `π₁(M_{g,ν}) → Out°_lac(π̂_{g,ν})` an isomorphism? Here
  `π₁(M_{g,ν})` is the étale fundamental group of the moduli stack over `ℚ`, `π̂_{g,ν}` the
  profinite fundamental group of its geometric fibre, and `Out°_lac(π̂_{g,ν})` the group of outer
  automorphisms fixing each cuspidal inertia class up to a common multiplier; this definition is
  the reading's, since the page's defining words are illegible. It would give
  `Gal(ℚ̄/ℚ) ≅ Out°_lac(π̂_{g,ν}) / T̂_{g,ν}` for every `(g, ν)`, `T̂_{g,ν}` the image of the
  geometric fundamental group (the profinite Teichmüller group), and at `(0, 3)`
  `Gal(ℚ̄/ℚ) ≅ Out°_lac(F̂₂)`. A marginal note gives a weaker form: `π₁(M_{g,ν})` is the
  normaliser of `T̂_{g,ν}` in `Out°_lac(π̂_{g,ν})`. Status: open. What is known is the injectivity
  of the outer Galois representation `Gal(ℚ̄/ℚ) → Out(π̂)` of a hyperbolic curve over `ℚ` (Belyi
  at `(0, 3)`; Matsumoto, and Hoshi and Mochizuki); no surjectivity onto `Out°_lac` is known.
  Missing: the moduli stacks `M_{g,ν}` over `ℚ`, the étale fundamental group of a stack with its
  outer action on that of the fibre, the étale fundamental group of `ℙ¹ − {0, 1, ∞}` with the
  outer Galois action (needed even for the `(0, 3)` form), and cusps with their inertia classes.
  The group-theoretic side alone (`F̂₂` and its outer automorphisms preserving three inertia
  classes up to a common multiplier) would need the profinite completion of a free group and
  `Ẑ`-powers in a profinite group; it is not the conjecture, and is not stated either.

## References

* the note on the open problems of the Montpellier notes (`docs/problems/article.tex`), section
  « Moduli of curves and Galois actions », problems p:gal and p:nc
* A. Grothendieck, folder 142, pp. 94–95, 98–101, *Action de Galois sur Teichmüller*
* A. Grothendieck, folder 147, pp. 148–151, *Structure à l'infini des `M_{g,ν}`*
* A. Grothendieck, folder 143, pp. 28–30 (finding `143-moduli-outlac-conjecture`)
-/
