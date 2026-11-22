module

public import Grothendieck.Folder145

@[expose] public section

/-!
# Folder 145, pages 34–35: the unit-exponent exercise

The proof of the trusted statement of `Challenge.Folder145`, by
`Grothendieck.Folder145.dihedral_witness`.
-/

open DihedralGroup

namespace Challenge.Folder145

theorem dihedral_witness (N : ℕ) {m : ℕ} (hm : Odd m) :
    ((sr 0 * sr 1 : DihedralGroup N)⁻¹) ^ m * (sr 0) ^ m * (sr 1) ^ m = 1 ↔
      (m : ZMod N) = 1 :=
  @Grothendieck.Folder145.dihedral_witness N _ hm

end Challenge.Folder145
