module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.Topology.Algebra.Group.PrimeToPQuotient
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 34, pages 153–155: local 1-asphericity of complete intersections, stated

Finding `34-lci-local-1-asphericity` (chapter « IV », 5.5–5.6). *If `f : X → S` over a strictly
local trait is flat, its closed fibre `X₀` is a local complete intersection, and the non-smooth
locus of `X₀` has codimension `≥ 2` in `X₀`, then `f` is locally 1-aspherical for the primes
`≠ p`; in particular, for `f` proper, specialisation `H¹(X₀, G) → H¹(X_η̄, G)` is bijective for
every finite group `G` of order prime to `p`.*

Nothing here is proved; a `def … : Prop` asserts nothing.

**The form stated.** The « in particular » for proper `f`, in the language of AxiomMath/Stacks:
a specialisation map `sp : π₁(X_η̄) → π₁(X_s̄)` (`AlgebraicGeometry.IsSpecializationMap`, SGA 1
XIII 2.10) induces an isomorphism of the maximal prime-to-`p` quotients
(`PrimeToP p`). Bijectivity of `H¹(−, G)` for every finite `G` of order prime to `p` is the same
statement, since `H¹(Y, G)` is `Hom(π₁(Y), G)` up to conjugacy. Stacks proves it for **smooth**
proper `f` (`AlgebraicGeometry.exists_continuousMulEquiv_primeToP_of_isProP_ker`, SGA 1 X 3.8,
under the descent hypothesis on the kernel); the page's content is the replacement of
smoothness by the two conditions on the closed fibre.

* The base is `Spec R` for a strictly henselian discrete valuation ring `R` (a strictly local
  trait), `p` its residue characteristic, taken prime (the equal-characteristic-zero case has
  no prime to exclude and is left out).
* The conditions on `X₀` are read on the geometric closed fibre `X_s̄ = X ×_S s̄`: the residue
  field of `R` is separably closed, so the two fibres differ by a purely inseparable extension,
  which changes neither being a local complete intersection nor the dimension of the local rings.
  Codimension `≥ 2` of the non-smooth locus is: every point outside the smooth locus has a
  local ring of dimension `≥ 2`.
* Flatness is the page's; properness and geometric connectedness are what the specialisation map
  of Stacks needs. Finite presentation is automatic over the noetherian `R` and is assumed for
  the smooth locus to be defined.

**Not stated.** Local 1-asphericity itself (vanishing of the local prime-to-`p` `H¹` on the
punctured strict localisations, 5.1–5.3) for `f` not proper: Stacks has no local asphericity.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Stacks.FundamentalGroup

universe u

namespace OpenProblems.Findings.Folder34

/-- The geometric closed fibre `X_s̄ ⟶ s̄` of `f`. -/
noncomputable abbrev fibreMap {X S : Scheme.{u}} (f : X ⟶ S) (s : GeometricPoint S) :
    fiberOverGeometricPoint f s ⟶ s.source :=
  pullback.snd f s.hom

/-- The non-smooth locus of the geometric closed fibre has codimension `≥ 2`: every point outside
the smooth locus of `X_s̄ ⟶ s̄` has a local ring of dimension at least `2`. -/
def NonSmoothLocusCodimTwo {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (s : GeometricPoint S) : Prop :=
  ∀ x : fiberOverGeometricPoint f s, x ∉ (fibreMap f s).smoothLocus →
    2 ≤ ringKrullDim ((fiberOverGeometricPoint f s).presheaf.stalk x)

/-- **Folder 34, 5.6, the proper case.** Let `R` be a strictly henselian discrete valuation ring
with residue characteristic a prime `p`, and `f : X → Spec R` proper, flat and with geometrically
connected fibres. Let `s̄` lie over the closed point and `η̄` over the generic point. If the
geometric closed fibre is a local complete intersection whose non-smooth locus has codimension
`≥ 2`, then every specialisation map `π₁(X_η̄) → π₁(X_s̄)` induces an isomorphism of the maximal
prime-to-`p` quotients. -/
@[montpellier "34, 153–155"]
def LciLocalOneAsphericity : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [StrictlyHenselianLocalRing R] (p : ℕ), p.Prime → ringChar (ResidueField R) = p →
    ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyConnected f]
      [LocallyOfFinitePresentation f] (s' s : GeometricPoint (Spec (.of R))),
      s.LiesOver (closedPoint R) →
      s'.LiesOver (genericPoint (Spec (.of R))) →
      IsLocalCompleteIntersectionMorphism (fibreMap f s) →
      NonSmoothLocusCodimTwo f s →
      ∀ (x' : GeometricPoint (fiberOverGeometricPoint f s'))
        (x : GeometricPoint (fiberOverGeometricPoint f s))
        (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        IsSpecializationMap f s' s x' x sp →
          ∃ e : PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x') ≃ₜ*
              PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
            ∀ g, e (primeToPMk p _ g) = primeToPMk p _ (sp g)

end OpenProblems.Findings.Folder34
