import Grothendieck.Folder80Maps2

/-!
# Pseudoline arrangements: the numbering lemma, stated as a proposition

Section « Pseudoline arrangements » of the note on the open problems of the Montpellier notes
(`docs/problems/article.tex`) holds no open problem any more: its boxed dichotomy (folder 80,
pp. 20, 24) and the numbering lemma of p. 28 have a short proof there (the proof is the
edition's). The dichotomy is proved in Lean for combinatorial pseudoline maps, as
`Grothendieck.Folder80Maps2.PseudolineMap.map_dichotomy`. The numbering lemma is not formalised;
it is stated below as a `Prop`, with the definitions of `Grothendieck/Folder80Maps2.lean`, so
that it is on record. It is proved on paper, not open.

Not formalised either, and not stated: the passage from a topological arrangement of
pseudolines in the real projective plane to its combinatorial map (Mathlib has no pseudolines);
folders 80 and 154 are otherwise covered by `Grothendieck/Folder80*.lean` and
`Grothendieck/Folder154*.lean`.
-/

namespace OpenProblems.Pseudolines

open Grothendieck.Folder80Maps2

variable {D L : Type*}

/-- The vertices of the partial arrangement formed by the lines of `S`: the vertices of the map
through two distinct lines of `S`. -/
def PartialVtx (X : PseudolineMap D L) (S : Set L) : Type _ :=
  {v : X.M.Vtx // ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ X.On v a ∧ X.On v b}

/-- Incidence in the partial arrangement formed by the lines of `S`. -/
def PartialOn (X : PseudolineMap D L) (S : Set L) : PartialVtx X S → S → Prop :=
  fun v l => X.On v.1 l.1

/-- **The numbering lemma** (folder 80, p. 28; the proof is the edition's, in the note's
Proposition of § Pseudoline arrangements). The lines of a bigon-free pseudoline map can be
numbered `ℓ₀, ℓ₁, …` so that the first four form a `II_4` or the first six a complete quadrangle
`III_6`, and every partial arrangement `{ℓ₀, …, ℓ_{k-1}}` from there on is bigon-free.

Status: proved on paper, not formalised. Choices: the arrangement is a combinatorial
`PseudolineMap` of `Grothendieck/Folder80Maps2.lean` with finitely many flags and lines; the
partial arrangements are read on the incidence (`PartialOn`), a vertex of the partial arrangement
being a vertex of the map met by two of its lines. -/
def NumberingLemma : Prop :=
  ∀ {D L : Type} [Fintype D] [Finite L] (X : PseudolineMap D L), BigonFree X.On →
    ∃ (n : ℕ) (e : Fin n ≃ L) (k₀ : ℕ),
      ((k₀ = 4 ∧ IsII4 (PartialOn X (e '' {i | (i : ℕ) < 4}))) ∨
        (k₀ = 6 ∧ HasIII6 (PartialOn X (e '' {i | (i : ℕ) < 6})))) ∧
      ∀ k, k₀ ≤ k → k ≤ n → BigonFree (PartialOn X (e '' {i | (i : ℕ) < k}))

end OpenProblems.Pseudolines
