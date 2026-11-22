/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint

/-!
# Folder 100, pages 30–38: the curve criterion for algebraising formal abelian schemes, stated

Finding `100-formal-abelian-curve-criterion`. *A formal abelian scheme over `Spf R`, `R` a
complete noetherian local ring, is algebraizable if and only if its pull-back to `Spf B′` is
algebraizable for every one-dimensional integral quotient `B` of `R` with normalisation `B′`.*

Nothing here is proved; a `def … : Prop` asserts nothing.

## Implementation notes

**Formal abelian schemes.** AxiomMath/Stacks has abelian schemes
(`AlgebraicGeometry.IsAbelianScheme`) but no formal schemes of this kind, so a formal abelian scheme over `Spf R` (for the adic
topology of an ideal `I`) is written as what it is by definition: a compatible system of abelian
schemes `Aₙ` over `Spec (R ⧸ I^(n+1))` with isomorphisms of group schemes
`A_{n+1} ×_{R/I^(n+2)} R/I^(n+1) ≅ Aₙ` (`FormalAbelianScheme`). It is *algebraizable*
(`FormalAbelianScheme.IsAlgebraizable`) when there is an abelian scheme `G` over `Spec R` and
isomorphisms `G ×_R R/I^(n+1) ≅ Aₙ` compatible with the transition isomorphisms; this is the
case `φ = id` of `FormalAbelianScheme.IsAlgebraizableAlong`, algebraizability of the pull-back
along a ring map `φ : R → R'`.

**The base change to `B′`.** For a one-dimensional integral quotient `B = R ⧸ 𝔭` of a complete
local `R`, the normalisation `B′` (the integral closure of `B` in its fraction field) is a
complete discrete valuation ring, finite over `B`; the `𝔪_R`-adic and `𝔪_{B′}`-adic topologies
on `B′` agree, so `Spf B′` is taken for the `𝔪_R B′`-adic topology, and the pull-back of the
system is its levelwise base change along `R ⧸ 𝔪^(n+1) → B′ ⧸ (𝔪B′)^(n+1)`; its
algebraizability is `IsAlgebraizableAlong` for `R → B → B′`. (That the levelwise base change is
again a formal abelian scheme is not needed for the statement and is not proved.)

## Not formalised

**Not stated.** The equivalent condition (iii) of page 30 (algebraizable after some proper
surjective `S′ → Spec R`) and the Proposition of page 36 on `S_red`.

## References

* A. Grothendieck, folder 100, pp. 30–38 (finding `100-formal-abelian-curve-criterion`)
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace OpenProblems.Findings.Folder100Formal

/-- Base change of schemes over `Spec A` along a ring map `A → B`. -/
noncomputable abbrev bc {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    Over (Spec (.of A)) ⥤ Over (Spec (.of B)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom φ))

/-- The canonical identification `bc χ ≅ bc φ ⋙ bc ψ` when `χ = ψ ∘ φ`. -/
noncomputable def bcComp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ) : bc χ ≅ bc φ ⋙ bc ψ :=
  eqToIso (by
    subst h
    simp only [bc, CommRingCat.ofHom_comp, Spec.map_comp]) ≪≫
    Over.pullbackComp (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ))

/-- The ring of level `n` of the `I`-adic system: `R ⧸ I^(n+1)`. -/
abbrev level {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) : Type u := R ⧸ I ^ (n + 1)

/-- The transition map `R ⧸ I^(n+2) → R ⧸ I^(n+1)`. -/
noncomputable def transition {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    level I (n + 1) →+* level I n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

theorem transition_comp_mk {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    (transition I n).comp (Ideal.Quotient.mk (I ^ (n + 1 + 1))) = Ideal.Quotient.mk (I ^ (n + 1)) :=
  Ideal.Quotient.factor_comp_mk _

/-- A **formal abelian scheme** over `Spf R` for the `I`-adic topology: abelian schemes `Aₙ` over
`Spec (R ⧸ I^(n+1))` with isomorphisms of group schemes `A_{n+1} ×_{R/I^(n+2)} R/I^(n+1) ≅ Aₙ`. -/
structure FormalAbelianScheme {R : Type u} [CommRing R] (I : Ideal R) where
  /-- The abelian scheme of level `n`. -/
  A : (n : ℕ) → Grp (Over (Spec (.of (level I n))))
  isAbelianScheme (n : ℕ) : IsAbelianScheme (A n).X
  /-- The transition isomorphisms. -/
  iso (n : ℕ) : (bc (transition I n)).mapGrp.obj (A (n + 1)) ≅ A n

namespace FormalAbelianScheme

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- The level-`n` map `R ⧸ I^(n+1) → R' ⧸ (φ(I)R')^(n+1)` induced by `φ : R → R'`. -/
noncomputable def levelMap {R' : Type u} [CommRing R'] (φ : R →+* R') (n : ℕ) :
    level I n →+* level (I.map φ) n :=
  Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])

theorem levelMap_comm {R' : Type u} [CommRing R'] (φ : R →+* R') (n : ℕ) :
    (transition (I.map φ) n).comp (levelMap φ (n + 1)) = (levelMap φ n).comp (transition I n) := by
  ext x
  rfl

/-- The compatibility of the isomorphisms `eₙ : G ×_{R'} R'/J^(n+1) ≅ Aₙ ×_{R/I^(n+1)} R'/J^(n+1)`
with the transition isomorphisms: the square at level `n`, read on the underlying schemes. -/
def Compatible (X : FormalAbelianScheme I) {R' : Type u} [CommRing R'] (φ : R →+* R')
    (G : Grp (Over (Spec (.of R'))))
    (e : ∀ n, (bc (Ideal.Quotient.mk ((I.map φ) ^ (n + 1)))).mapGrp.obj G ≅
      (bc (levelMap φ n)).mapGrp.obj (X.A n)) (n : ℕ) : Prop :=
  let a := (bcComp (Ideal.Quotient.mk ((I.map φ) ^ (n + 1 + 1))) (transition (I.map φ) n)
    (Ideal.Quotient.mk ((I.map φ) ^ (n + 1))) (transition_comp_mk (I.map φ) n)).hom.app G.X
  let b := (bc (transition (I.map φ) n)).map (e (n + 1)).hom.hom.hom
  let c := (bcComp (levelMap φ (n + 1)) (transition (I.map φ) n)
    ((levelMap φ n).comp (transition I n)) (levelMap_comm φ n)).inv.app (X.A (n + 1)).X
  let d := (bcComp (transition I n) (levelMap φ n)
    ((levelMap φ n).comp (transition I n)) rfl).hom.app (X.A (n + 1)).X
  let f := (bc (levelMap φ n)).map (X.iso n).hom.hom.hom
  (((a ≫ b) ≫ c) ≫ d) ≫ f = (e n).hom.hom.hom

/-- The pull-back of `X̂` along `φ : R → R'` is **algebraizable**: there are an abelian scheme `G`
over `Spec R'` and isomorphisms of group schemes `G ×_{R'} R'/J^(n+1) ≅ Aₙ ×_{R/I^(n+1)} R'/J^(n+1)`
(`J = φ(I)R'`), compatible with the transition isomorphisms of `X̂`, base changed, and the
canonical ones of `G` (`Compatible`). For `φ = id` this is algebraizability of `X̂` itself. -/
def IsAlgebraizableAlong (X : FormalAbelianScheme I) {R' : Type u} [CommRing R']
    (φ : R →+* R') : Prop :=
  ∃ (G : Grp (Over (Spec (.of R')))) (_ : IsAbelianScheme G.X)
    (e : ∀ n, (bc (Ideal.Quotient.mk ((I.map φ) ^ (n + 1)))).mapGrp.obj G ≅
      (bc (levelMap φ n)).mapGrp.obj (X.A n)),
    ∀ n, X.Compatible φ G e n

/-- `X̂` is **algebraizable**: its pull-back along the identity of `R` is. -/
def IsAlgebraizable (X : FormalAbelianScheme I) : Prop :=
  X.IsAlgebraizableAlong (RingHom.id R)

end FormalAbelianScheme


/-- **Folder 100, page 30, the curve criterion.** Let `R` be a complete noetherian local ring. A
formal abelian scheme over `Spf R` (for the `𝔪`-adic topology) is algebraizable if and only if,
for every prime `𝔭` of `R` with `R ⧸ 𝔭` of dimension one, its pull-back to the normalisation `B′`
of `B = R ⧸ 𝔭` is algebraizable. -/
def CurveCriterion : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (X : FormalAbelianScheme (maximalIdeal R)),
    X.IsAlgebraizable ↔
      ∀ (𝔭 : Ideal R) [𝔭.IsPrime], ringKrullDim (R ⧸ 𝔭) = 1 →
        X.IsAlgebraizableAlong
          ((algebraMap (R ⧸ 𝔭) (integralClosure (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭)))).comp
            (Ideal.Quotient.mk 𝔭))

end OpenProblems.Findings.Folder100Formal
