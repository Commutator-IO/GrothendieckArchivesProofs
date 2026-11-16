/-!
# Folder 94: a representability criterion for functors on modules, not stated

The open row `94-representability-criterion` of the edition's list of findings
(`src/content/findings.ts`), folder 94, pp. 15–16 (Théorème 12). It is not stated; why.

* `94-representability-criterion`: for a noetherian ring `A` quotient of a regular ring (the
  reading fixes `A` excellent), a functor `F : Mod(A) → Ens` is `Hom_A(P, −)` with `P` finite iff
  it commutes with filtered colimits, is left exact, satisfies an `m_p`-adic and a `g`-adic
  completion condition on finite modules, sends finite modules to finite modules, has a
  constructible fibre-dimension function `p ↦ dim F(k(p))`, and, for every quotient `B` and
  finite `B`-module `Ω`, commutes generically with reduction of `Ω` modulo systems of parameters;
  preservation of products is not among the conditions. Status: candidate. Missing or unsettled:
  conditions (iv)–(vi) use the `A`-module structure that a left exact set-valued functor acquires
  and the `k(p)`-structure on `F(k(p))`, which would have to be constructed; Mathlib has no
  systems of parameters of a noetherian local ring, which condition (vi) quantifies over, and a
  word above « quotient » in (vi) is unread. The reading itself leaves the sufficiency resting on
  the converse of Rem. 5 bis under the global finiteness (iv), which it does not settle, and
  restricts to `A` excellent; a faithful statement would have to choose between the page's
  hypothesis and the reading's.
-/
