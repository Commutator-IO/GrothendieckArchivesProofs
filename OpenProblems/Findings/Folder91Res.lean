module

public import OpenProblems.Findings.Folder91
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 91, pages 24–28 and 31: representability of `Res_{X/S}(P)` by a scheme, stated

Finding `91-res-representable-by-scheme`. *For `X` proper, flat and of finite presentation over
`S` and `P → X` locally of finite presentation (and separated), the Weil restriction
`Res_{X/S}(P)` is representable by a scheme — not only an algebraic space — under three
conditions on finitely many closed subschemes `Zᵢ` of `X`: (a) each `Res_{Zᵢ/S}(P|Zᵢ)` is
representable; (b) `X` is normally flat along each `Zᵢ`; (c) every associated point of a geometric
fibre of `X → S` lies in `⋃ Zᵢ`.*

Nothing here is proved; a `def … : Prop` asserts nothing. The Weil restriction is
`OpenProblems.Findings.Folder91.weilRestriction`, its functor of points on `S`-schemes.

**Normal flatness** (`IsNormallyFlatAlong`) is read on stalks: for a closed immersion
`i : Z → X` and `z ∈ Z`, let `J` be the kernel of `𝒪_{X,i(z)} → 𝒪_{Z,z}`; `X` is normally flat
along `Z` when every `Jⁿ/Jⁿ⁺¹` is a flat `𝒪_{X,i(z)}/J`-module (EGA IV 6.10.1). `Jⁿ/Jⁿ⁺¹` is
written `Jⁿ ⧸ J • Jⁿ`.

**Associated points of a geometric fibre** (`IsAssociatedPoint`): `x` is associated when the
maximal ideal of `𝒪_{Y,x}` is an associated prime of `𝒪_{Y,x}` (EGA IV 3.1.1); the geometric
fibres are taken over the algebraic closures of the residue fields, as in `Folder91`.

**Not stated.** The conclusions (ii) and (iii) (openness and quasi-projectivity on
quasi-compact parts) and Corollaries 2–9: their hypotheses carry the uncertain readings noted
in the finding (« lisse », « ouverte »).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
open OpenProblems.Findings.Folder91

universe u

namespace OpenProblems.Findings.Folder91Res

/-- `X` is **normally flat along** the closed subscheme `i : Z → X`: at every `z ∈ Z`, with `J` the
kernel of `𝒪_{X,i(z)} → 𝒪_{Z,z}`, every `Jⁿ/Jⁿ⁺¹` is flat over `𝒪_{X,i(z)}/J`. -/
def IsNormallyFlatAlong {X Z : Scheme.{u}} (i : Z ⟶ X) : Prop :=
  ∀ (z : Z) (n : ℕ),
    let J := RingHom.ker (i.stalkMap z).hom
    Module.Flat (X.presheaf.stalk (i z) ⧸ J)
      (↥(J ^ n) ⧸ J • (⊤ : Submodule (X.presheaf.stalk (i z)) ↥(J ^ n)))

/-- `x` is an **associated point** of the scheme `Y`: the maximal ideal of `𝒪_{Y,x}` is an
associated prime of `𝒪_{Y,x}`. -/
def IsAssociatedPoint (Y : Scheme.{u}) (x : Y) : Prop :=
  maximalIdeal (Y.presheaf.stalk x) ∈ associatedPrimes (Y.presheaf.stalk x) (Y.presheaf.stalk x)

/-- The restriction `P ×_X Z` of an `X`-scheme `P` to `i : Z → X`, as a `Z`-scheme. -/
noncomputable abbrev restrictTo {X Z : Scheme.{u}} (i : Z ⟶ X) (P : Over X) : Over Z :=
  (Over.pullback i).obj P

/-- **Folder 91, page 25, conclusion (i).** Let `f : X → S` be proper, flat and of finite
presentation and `P → X` separated and locally of finite presentation. Let `Zᵢ → X` (`i ∈ ι`,
finite) be closed immersions such that (a) each `Res_{Zᵢ/S}(P ×_X Zᵢ)` is representable,
(b) `X` is normally flat along each `Zᵢ`, and (c) every associated point of every geometric fibre
`X ×_S Spec κ(s)‾` lies over a point of some `Zᵢ`. Then `Res_{X/S}(P)` is representable. -/
@[montpellier "91, 25"]
def ResRepresentableByScheme : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (P : Over X) [IsSeparated P.hom] [LocallyOfFinitePresentation P.hom]
    (ι : Type u) [Finite ι] (Z : ι → Scheme.{u}) (i : ∀ k, Z k ⟶ X)
    [∀ k, IsClosedImmersion (i k)],
    (∀ k, (weilRestriction (i k ≫ f) (restrictTo (i k) P)).IsRepresentable) →
    (∀ k, IsNormallyFlatAlong (i k)) →
    (∀ (s : S) (x : ↥(pullback f (algClosurePoint S s))),
      IsAssociatedPoint (pullback f (algClosurePoint S s)) x →
        ∃ k, ∃ z : Z k, i k z = pullback.fst f (algClosurePoint S s) x) →
    (weilRestriction f P).IsRepresentable

end OpenProblems.Findings.Folder91Res
