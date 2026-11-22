module

public import Grothendieck.Folder1

@[expose] public section

/-!
# Folder 1, page 124: Corollaire 3 in finite dimension

The proof of the trusted statement of `Challenge.Folder1`, by `Grothendieck.Folder1.corollaire3`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Challenge.Folder1

theorem corollaire3 {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    ‖det (1 + (A + B))‖ ≤
        ((det (1 + (CFC.abs A + CFC.abs B))).re + (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re) / 2 ∧
      ‖det (1 + (A + B))‖ ^ 2 ≤
        (det (1 + (CFC.abs A + CFC.abs B))).re * (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re :=
  @Grothendieck.Folder1.corollaire3 _ _ _ A B

end Challenge.Folder1
