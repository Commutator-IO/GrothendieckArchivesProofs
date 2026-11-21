module

/-!
# Folder 161-2: rings of definite characteristic as a join of subtopoi, not stated

The open row `161-2-definite-characteristic-join-of-subtopoi` of the edition's list of findings
(`src/content/findings.ts`), folder 161-2, pp. 47–49 (*Algèbre universelle*). It cannot be stated
faithfully with Mathlib and the Stacks library; what is missing. The neighbouring problem
p:noncoh (same folder) is in `OpenProblems/TopoiStacks.lean`.

* `161-2-definite-characteristic-join-of-subtopoi`: the rings locally of characteristic `p` for
  some prime `p` or of characteristic `0` are classified by a subtopos of the classifying topos of
  rings which is not coherent and not presented by an open condition, but is the join of the open
  subtopos `X_{car > 0} = ⋃_p X_{ℤ/p}` and the non-open subtopos `X_ℚ = ⋂_n X_{ℤ[1/n]}`; and the
  join of two subtopoi `V, W` is obtained by gluing along an open under conditions on opens `Z'`
  of `V` and `Z''` of `W`. Status: candidate. Missing: the classifying topos of a geometric
  theory and the subtopoi classifying its quotient theories, coherent topoi, and the lattice of
  subtopoi with its joins; the Stacks library has subtopoi of a topos of sheaves, open and closed
  ones (`IsSubtopos`, `IsOpenSubtopos`, `IsClosedSubtopos`, Stacks 08LV, 08LX, 08LZ), but not the
  join. « Obtained by gluing along an open » is the edition's form of a brouillon (p. 48) and is
  not a defined construction there, so the gluing criterion has no statement yet to formalise.
-/
