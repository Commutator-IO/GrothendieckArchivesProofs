/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Buffalo.AG.Part05a
public import Buffalo.AG.Part05b
public import Buffalo.AG.Part05c

/-!
# Buffalo, algebraic geometry, part 05: (undated session, from 7:04:25) – 25 June 1973 (to 0:57:01)

The entries of `docs/buffalo-ag/index.tex` lines 632–769, split by session into `Part05a`
(`thSz9ZHDK9o`, 7:04:25–8:54:39: Zariski sheaves, projective bundles, `𝔾_m`), `Part05b`
(`thSz9ZHDK9o`, 8:56:26–10:31:34: fibres, relative spectrum, fibre products, localization at a
point) and `Part05c` (`Oqhr-Gt66es`, 0:00:01–0:57:01: local, noetherian and artinian schemes,
finiteness conditions), all in the namespace `Buffalo.AG.Part05`. The status of each entry is in
`docs/buffalo-ag/lean/Part05.json`.

## Main results

* `prop_26850`: a morphism of schemes is locally surjective for the Zariski topology if and only
  if it has local sections.
* `prop_25594`: the restriction of a Zariski sheaf on `Sch/S` to the small Zariski site is a
  sheaf.
* `prop_30775`, `prop_30838`: two epimorphisms `M → R` with the same kernel differ by a unit, and
  `𝔾_m` acts freely and transitively on them.
* `prop_28630`, `prop_28693`, `prop_29157`, `prop_29932`, `prop_30256`, `prop_32079`,
  `prop_32506`: the ring-theoretic content of the projective bundle.
* `cex_1295`, `ex_1556`: one-point spectra that are not fields.
* Corrected: `Oqhr-Gt66es-1556` (`k[t]/(t^n)` and `ℤ/p^nℤ` are spectra of fields for `n = 1`;
  the entry needs `n ≥ 2`, `ex_1556_one`).

## Not formalised

No carrier in mathlib: the projective bundle `𝐏(ℳ)` as a functor on `Sch/S` and its
representability and universal quotient, Grassmannian and flag bundles, quasi-coherent algebras
and the relative spectrum, the restriction of sheaves from the big to the small Zariski site and
its commutation with colimits.

## References

* the Buffalo lectures on algebraic geometry (1973), undated session (from 7:04:25) – 25 June
  1973 (to 0:57:01), videos `thSz9ZHDK9o` and `Oqhr-Gt66es` (`docs/buffalo-ag/index.tex`,
  lines 632–769)
-/

@[expose] public section

