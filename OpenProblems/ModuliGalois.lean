module

/-!
# Moduli of curves and Galois actions: the open problems, not stated

Section « Moduli of curves and Galois actions » of the note on the open problems of the
Montpellier notes (`docs/problems/article.tex`): problems p:gal and p:nc. Neither can be stated
faithfully with Mathlib and the Stacks library; for each, what is missing.

* p:gal (folder 142, pp. 94–95, 98–101, *Action de Galois sur Teichmüller*, [from 1978]): for an
  anabelian (hyperbolic) curve `X` over a field `K` of finite type over `ℚ`, are the page's
  conditions on a vertex-fixing automorphism of the profinite fundamental groupoid
  `Π̂₁(X, I)` (lifting to the finite étale covers defined over `K`, preserving the kernels
  attached to `K`-morphisms, compatibility with morphisms between covers, the loop condition at
  the cusps with a single multiplier) sufficient for it to come from `Gal(K̄/K)`? Status: open
  (Pop's theorem and its tripod variants need bases of dimension greater than one). Missing: the
  profinite étale fundamental groupoid on several base points with its functoriality in finite
  étale covers, hyperbolic curves, cusps and their inertia, and the outer Galois action. Mathlib
  has Galois categories and fibre functors, and Stacks has pieces of the étale fundamental group,
  but not this groupoid with its Galois action.
* p:nc (folder 147, pp. 148–151, *Structure à l'infini des `M_{g,ν}`*, winter 1982–1983): is the
  deleted tubular neighbourhood of a normal crossings divisor `Θ` in a smooth complex analytic
  space (or orbifold) the homotopy colimit of the deleted neighbourhoods of the strata of its
  unfolding, so that its fundamental groupoid is the amalgamated sum of the groupoids of the
  torus bundles over the strata of codimension 1 and 2? Status: open (not found in this form;
  the two-level principle for the discrete tower is Hatcher, Lochak and Schneps). Missing:
  complex analytic spaces and orbifolds, normal crossings divisors and their unfolding, tubular
  neighbourhoods, homotopy colimits of spaces, and fundamental groupoids of stratified spaces.
-/
