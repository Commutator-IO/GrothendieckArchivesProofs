import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Pullback

/-!
# Buffalo, algebraic geometry, part 09: inverse image of ample sheaves

Entry `19516` of the index (« ampleness of an invertible sheaf is preserved under inverse image and
under passing to the norm »), stated with the definitions of the AxiomMath/Stacks project (see
`Part07AmpleStacks.lean` for the conventions).

**What is proved.**
* `prop_19516`: the inverse image of an ample invertible sheaf along a quasi-affine morphism (in
  particular along a finite or an affine morphism) is ample (Stacks tag 0892 (2), EGA II 5.1.12).
  Absolute ampleness is not preserved by an arbitrary inverse image (pull `𝒪(1)` on `ℙ¹` back to
  `ℙ¹ × ℙ¹`), so the quasi-affine hypothesis is the correct reading of the entry.

**Not formalised.** The norm of an ample sheaf along a finite locally free morphism (19516, second
half; 18872), the uniform very ample power of 18420, the descent statements 18219, 18281, 18808,
20037, 24670, 24799 and the quasi-projectivity over a field extension 19653: AxiomMath/Stacks has
no norm of invertible sheaves nor descent data of schemes.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Buffalo.AG.Part09

/-- vuys5SNs2eQ-19516 (5:25:16) [prop] (inverse image) If `f : X → S` is quasi-affine and `M` is
an ample invertible sheaf on `S`, then `f^* M` is ample on `X` (Stacks tag 0892 (2),
EGA II 5.1.12). -/
theorem prop_19516 {X S : Scheme.{u}} (f : X ⟶ S) [IsQuasiAffineHom f] (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M) :
    Stacks.Ample.IsAmple X
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj M) :=
  Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom f M hM

end Buffalo.AG.Part09
