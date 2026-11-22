/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Buffalo.AG.Part08c

/-!
# Buffalo, algebraic geometry, part 08: 6 July 1973 (from 10:19:03) – 10 July 1973 (to 4:14:24)

The entries of `docs/buffalo-ag/index.tex` lines 1054–1190 (videos `Oqhr-Gt66es`, 10:19:03–10:52:45,
and `vuys5SNs2eQ`, 0:00:02–4:14:24), split into `Part08a` (flatness, criteria, base change),
`Part08b` (descent of properties of morphisms and modules, topological descent) and `Part08c`
(closures of images, descent of subsets, monomorphisms that are not immersions, Chevalley,
integrality), all in the namespace `Buffalo.AG.Part08`. The status of each entry is in
`docs/buffalo-ag/lean/Part08.json`.

## Main results

* `prop_131`, `closure_image_mem_irreducibleComponents`: the generalizing criterion through
  irreducible components.
* `prop_584`, `prop_587`: flatness over a Dedekind ring through minimal and associated primes.
* `prop_520`: filtered colimits of flat modules.
* `prop_2750`, `prop_2620`, `prop_6088`: descent of quasi-compactness, quasi-separation,
  radiciality and monomorphisms along (faithfully flat) surjective quasi-compact maps.
* `prop_5323`: topological descent of open, closed, generalizing maps and homeomorphisms.
* `prop_10517`, `prop_10644`: descent of subsets and open sets.
* the counterexamples `cex_3950`, `cex_10967`, `cex_12606`.

## Not formalised

No carrier in mathlib: quasi-coherent modules on schemes as a pseudofunctor with descent data,
fpqc descent of morphisms and of affine schemes, Cohen–Macaulay rings, projective morphisms,
relative ampleness and `P(E)`.

## References

* the Buffalo lectures on algebraic geometry (1973), 6 July 1973 (from 10:19:03) – 10 July 1973
  (to 4:14:24), videos `Oqhr-Gt66es` and `vuys5SNs2eQ` (`docs/buffalo-ag/index.tex`,
  lines 1054–1190)
-/

@[expose] public section

