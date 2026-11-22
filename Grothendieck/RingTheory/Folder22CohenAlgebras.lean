/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import StacksFrontier.RingTheory.GeometricallyRegular.FormalSmoothness
import Grothendieck.Attr
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Folder 22, pages 12 to 18: formal smoothness and geometric regularity (3.9, 3.10, 3.12, 3.13)

The typescript of folder 22 (`transcripts/22/22.modern.tex`, pages 12–17) climbs from Cohen
algebras (Déf. 3.7) to the statement it calls the substance of the whole numéro:

> **Corollaire 3.13.** Soit `A → B` un homomorphisme local d'anneaux locaux noethériens. On
> suppose l'extension résiduelle `k(B)/k(A)` de multiplicité radicielle finie — par exemple
> séparable, ou de type fini — ou bien `𝔪_B = 𝔪_A B`. On munit `A` et `B` de leurs topologies
> habituelles. Alors les conditions suivantes sont équivalentes : (i) `B` est formellement lisse
> sur `A` ; (ii) `B` est plat sur `A`, et `B_0 = B ⊗_A k` est une algèbre universellement régulière
> sur `k`.

and page 18 asks (Question 1) whether a noetherian local `k`-algebra universally regular over a
field `k` is formally smooth over `k`, that is, whether the finiteness hypothesis on the residue
extension can be dropped. Grothendieck's « universellement régulière » is today's *geometrically
regular*, and the statement is Stacks 07NQ (EGA 0_IV 19.7.1, SGA 1 III 1.7). It is proved here
from AxiomMath/Stacks (Apache-2.0), `StacksFrontier/RingTheory/GeometricallyRegular/
FormalSmoothness.lean`.

## Main results

* `corollaire3_13`: for every local homomorphism `f : A → B` of noetherian local rings, `f` is
  formally smooth for the `𝔪_B`-adic topology if and only if `B` is flat over `A` and the special
  fibre `k ⊗_A B` is geometrically regular over `k = A/𝔪_A` (Stacks 07NQ). *No hypothesis on the
  residue extension is needed*: the radicial-multiplicity hypothesis, which the NB of page 14 says
  is used only to know that `B_0` is Cohen–Macaulay and is « très probablement inutile », is
  dropped, as is the handwritten alternative `𝔪_B = 𝔪_A B`.
* `question1`: over a field `k`, a noetherian local `k`-algebra is formally smooth for its
  `𝔪`-adic topology if and only if it is geometrically regular (Stacks 07EL in both
  characteristics, EGA 0_IV 22.5.8). This answers Question 1 of page 18 in the affirmative, with
  no finiteness hypothesis, and is the statement « 2.6 » that the proof of 3.13 invokes (« pour
  `B_0`, formellement lisse et universellement régulier coïncident »), absent from the folder.
* `isRegularLocalRing_of_formallySmoothNAdic`: such an algebra is a regular local ring (Stacks
  07EI), the fact the proof of 3.9 takes from « les résultats du numéro 2 ».
* `corollaire3_9`: `f` is formally smooth if and only if `B` is flat over `A` and `B_0` is
  formally smooth over `k` (Stacks 07NQ, (2) ⇔ (3)), again without the radicial hypothesis of 3.9.
* `corollaire3_10`: existence. If `A` is a complete noetherian local ring with residue field `k`
  and `B_0` a complete noetherian local `k`-algebra, formally smooth over `k` for its `𝔪`-adic
  topology, there is a complete noetherian local ring `B` and a local homomorphism `A → B`,
  formally smooth and flat, with `k ⊗_A B ≃ B_0` as `k`-algebras (Stacks 07NR, EGA 0_IV 19.7.2).
  The page's hypothesis that `K/k` be separable is not needed.
* `corollaire3_12_existence`: the case `B_0 = K` of 3.10, the existence half of Cor. 3.12: for a
  separable extension `K` of the residue field `k` of a complete noetherian local ring `A`, there
  is a complete noetherian local `A`-algebra `B`, flat and formally smooth, with `k ⊗_A B ≃ K` —
  a « Cohen ring » of `K` over `A` (EGA 0_III 10.3.1 for the flat local extension, which the
  proof of 3.10 quotes).

## Implementation notes

Formal smoothness is `RingHom.FormallySmoothNAdic f 𝔪_B` (Stacks 07NI, in the elementary form of
07EC (2)(b), as in `Grothendieck/RingTheory/Folder22Adic.lean`): square-zero lifting for maps
`B → C/J` that kill a power of `𝔪_B`, the source carrying the discrete topology. For a local
homomorphism this is formal smoothness for the two « topologies habituelles » of the page: a map
`A → C` whose composite with `C → C/J` kills `𝔪_Aⁿ` kills `𝔪_A^{2n}`, so it is continuous for the
`𝔪_A`-adic topology.

In `corollaire3_12_existence`, separability is Stacks' `Algebra.IsSeparableExtension` (every
finitely generated subextension separably generated); it gives formal smoothness of `K` over `k`
(`Algebra.FormallySmooth.iff_isSeparableExtension`, EGA 0_IV 19.6.1).

## Not formalised

* Cohen algebras themselves (Déf. 3.7) and the condition P (a strict countable projective system
  of projective modules), hence Lemme 3.2, Théorème 3.6, Cor. 3.8 (uniqueness of the Cohen algebra
  with a given special fibre, and the five equivalent forms), the identification of Cohen algebra
  with « complet et formellement lisse » in 3.9 and 3.11, and the descent of 3.11.
* The uniqueness halves of 3.10 and 3.12 (a formally smooth lift of `B_0` is unique up to
  isomorphism) and the equivalence 1) ⇔ 2) of 3.12 (formally smooth ⇔ flat with `K/k` separable
  when `𝔪_B = 𝔪_A B`) are not here: they are proved in
  `Grothendieck/RingTheory/Folder22Uniqueness.lean` (`corollaire3_10_uniqueness`,
  `corollaire3_12_uniqueness`, `corollaire3_12`).
* In 3.10, `A` is assumed complete; the page allows any noetherian local `A` (its `B` lives over
  `Â`).
* Questions 3) and 4) of pages 19–20 (openness of the formally smooth and flat loci). Question 2)
  is answered negatively in characteristic 0 by `Grothendieck.Folder22Adic.adic_not_discrete`.

## References

* A. Grothendieck, folder 22, typescript pp. 12–20 (`transcripts/22/22.modern.tex`)
* [EGA 0_III] 10.3.1; [EGA 0_IV] 19.6.1, 19.7.1, 19.7.2, 22.5.8
* [SGA 1] III 1.7
* Stacks Project, tags 07NQ, 07NI, 07EC, 07EL, 07EI, 07NR
-/

@[expose] public section


open IsLocalRing
open scoped TensorProduct

universe u v

namespace Grothendieck.Folder22CohenAlgebras

/-- Over a field of characteristic `p`, geometric regularity is formal smoothness for the
`𝔪`-adic topology (Stacks 07EL, (1) ⇔ (2)). -/
private theorem geometricallyRegular_iff_of_charP
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [IsNoetherianRing C] [IsLocalRing C] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Algebra.IsGeometricallyRegular k C ↔
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace C := (maximalIdeal C).adicTopology
  let : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology C C := (maximalIdeal C).isLinearTopology
  change Algebra.IsGeometricallyRegular k C ↔
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C)
  rw [← isFormallySmooth_iff_formallySmoothNAdic
    (algebraMap k C) (maximalIdeal C) (by rfl)]
  exact ((formalSmoothness_maximalIdeal_characterizations k C).2 p).out 1 2

/-- Over a field of characteristic `0`, the same (Stacks 07EL, characteristic `0`: regularity is
formal smoothness, and a regular ring is geometrically regular). -/
private theorem geometricallyRegular_iff_of_charZero
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [IsNoetherianRing C] [IsLocalRing C] [CharZero k] :
    Algebra.IsGeometricallyRegular k C ↔
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace C := (maximalIdeal C).adicTopology
  let : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology C C := (maximalIdeal C).isLinearTopology
  change Algebra.IsGeometricallyRegular k C ↔
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C)
  rw [← isFormallySmooth_iff_formallySmoothNAdic
    (algebraMap k C) (maximalIdeal C) (by rfl)]
  rw [← (formalSmoothness_maximalIdeal_characterizations k C).1]
  constructor
  · intro h
    have : IsRegularRing (k ⊗[k] C) := h.isRegularRing_tensorProduct k
    have : IsRegularRing C := IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.lid k C).toRingEquiv
    exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing C
  · intro h
    have : IsRegularRing C := ((IsLocalRing.isRegularRing_tfae (R := C)).out 1 3).mp h
    exact isGeometricallyRegular_of_isRegularRing_of_charZero k C

/-- **Question 1 of page 18, answered; the statement « 2.6 » invoked by 3.13.** Let `k` be a
field and `C` a noetherian local `k`-algebra. Then `C` is formally smooth over `k` for its
`𝔪`-adic topology if and only if it is geometrically (« universellement ») regular over `k`.
No hypothesis on the residue field, and no characteristic assumption. Stacks 07EL. -/
@[montpellier "22, 18", ega "0 22.5.8"]
theorem question1 (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [IsNoetherianRing C] [IsLocalRing C] :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C) ↔
      Algebra.IsGeometricallyRegular k C := by
  obtain hk | ⟨p, hp, hkp⟩ := CharP.exists' k
  · exact (geometricallyRegular_iff_of_charZero k C).symm
  · exact (geometricallyRegular_iff_of_charP k C p).symm

/-- A noetherian local algebra over a field, formally smooth for its `𝔪`-adic topology, is a
regular local ring (Stacks 07EI): the fact the proof of 3.9 takes from the numéro 2. -/
theorem isRegularLocalRing_of_formallySmoothNAdic (k : Type u) (C : Type v) [Field k]
    [CommRing C] [Algebra k C] [IsNoetherianRing C] [IsLocalRing C]
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C)) :
    IsRegularLocalRing C := by
  have hg : Algebra.IsGeometricallyRegular k C := (question1 k C).mp h
  have : IsRegularRing (k ⊗[k] C) := hg.isRegularRing_tensorProduct k
  have : IsRegularRing C := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.lid k C).toRingEquiv
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing C

section Local

variable {A : Type u} {B : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing B] [IsNoetherianRing B] [IsLocalRing B]

/-- **Corollaire 3.13**, without its hypothesis on the residue extension. A local homomorphism
`f : A → B` of noetherian local rings is formally smooth for the `𝔪_B`-adic topology if and only
if `B` is flat over `A` and the special fibre `B_0 = k ⊗_A B` is geometrically regular over the
residue field `k` of `A`. Stacks 07NQ, (3) ⇔ (1). -/
@[montpellier "22, 12–17", ega "0 19.7.1"]
theorem corollaire3_13 (f : A →+* B) [IsLocalHom f] :
    letI : Algebra A B := f.toAlgebra
    let k := ResidueField A
    let Bbar := k ⊗[A] B
    RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B) ↔
      Module.Flat A B ∧ Algebra.IsGeometricallyRegular k Bbar := by
  have h := flat_geometricallyRegular_specialFiber_formallySmooth_tfae f
  exact h.out 3 1

/-- **Corollaire 3.9**, 1) ⇔ 2), with « algèbre de Cohen » read as « formally smooth » and
without the radicial hypothesis: `f` is formally smooth if and only if `B` is flat over `A` and
`B_0 = k ⊗_A B` is formally smooth over `k` for its `𝔪`-adic topology. Stacks 07NQ, (3) ⇔ (2). -/
@[montpellier "22, 12–17"]
theorem corollaire3_9 (f : A →+* B) [IsLocalHom f] :
    letI : Algebra A B := f.toAlgebra
    let k := ResidueField A
    let Bbar := k ⊗[A] B
    RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B) ↔
      Module.Flat A B ∧
        RingHom.FormallySmoothNAdic.{max u v} (algebraMap k Bbar) (maximalIdeal Bbar) := by
  have h := flat_geometricallyRegular_specialFiber_formallySmooth_tfae f
  exact h.out 3 2

end Local

/-- **Corollaire 3.10 (existence)**, for a complete base and without the separability of the
residue extension. Let `A` be a complete noetherian local ring with residue field `k`, and `B_0` a
complete noetherian local `k`-algebra formally smooth over `k` for its `𝔪`-adic topology. Then
there are a complete noetherian local ring `B` and a local homomorphism `A → B`, formally smooth
for the `𝔪_B`-adic topology and flat, with special fibre `k ⊗_A B ≃ B_0` as `k`-algebras.
Stacks 07NR (existence) and 07NP (flatness). -/
@[montpellier "22, 12–17", ega "0 19.7.2"]
theorem corollaire3_10 {A : Type u} {B₀ : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [CommRing B₀] [IsNoetherianRing B₀] [IsLocalRing B₀] [IsAdicComplete (maximalIdeal B₀) B₀]
    [Algebra (ResidueField A) B₀]
    (hB : RingHom.FormallySmoothNAdic.{max u v}
      (algebraMap (ResidueField A) B₀) (maximalIdeal B₀)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B) (_ : IsAdicComplete (maximalIdeal B) B)
      (f : A →+* B) (_ : IsLocalHom f),
      RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B) ∧
        letI : Algebra A B := f.toAlgebra
        Module.Flat A B ∧ Nonempty ((ResidueField A ⊗[A] B) ≃ₐ[ResidueField A] B₀) := by
  obtain ⟨B, i1, i2, i3, i4, f, i5, hf, he⟩ := exists_completeLocal_formallySmooth_lift hB
  refine ⟨B, i1, i2, i3, i4, f, i5, hf, ?_⟩
  exact ⟨flat_of_isFormallySmooth_maximalIdeal_adic f hf, he⟩

/-- Formal smoothness of an algebra (mathlib's `Algebra.FormallySmooth`, discrete topology)
implies formal smoothness for every adic topology on the target. -/
private theorem formallySmoothNAdic_of_formallySmooth' {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S] (I : Ideal S) :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap R S) I := by
  intro T _ J hJ f ψ hψ _
  let : Algebra R T := f.toAlgebra
  let ψ' : S →ₐ[R] T ⧸ J :=
    { ψ with commutes' := fun r ↦ RingHom.congr_fun hψ r }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ ψ'
  refine ⟨g.toRingHom, congrArg AlgHom.toRingHom hg, ?_⟩
  ext r
  exact g.commutes r

/-- **Corollaire 3.12, existence**, for a complete base: the « Cohen ring » of a separable
extension. Let `A` be a complete noetherian local ring with residue field `k` and `K` a separable
extension of `k`. There are a complete noetherian local ring `B` and a local homomorphism
`A → B`, formally smooth and flat, whose special fibre `k ⊗_A B` is `K` as a `k`-algebra (whence
`𝔪_A B = 𝔪_B` and residue field `K`, not restated). This is the case `B_0 = K` of 3.10, the one
the proof of 3.10 takes from EGA 0_III 10.3.1. -/
@[montpellier "22, 12–17"]
theorem corollaire3_12_existence {A : Type u} {K : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [Field K] [Algebra (ResidueField A) K] [Algebra.IsSeparableExtension (ResidueField A) K] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B) (_ : IsAdicComplete (maximalIdeal B) B)
      (f : A →+* B) (_ : IsLocalHom f),
      RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B) ∧
        letI : Algebra A B := f.toAlgebra
        Module.Flat A B ∧ Nonempty ((ResidueField A ⊗[A] B) ≃ₐ[ResidueField A] K) := by
  have : Algebra.FormallySmooth (ResidueField A) K :=
    (Algebra.FormallySmooth.iff_isSeparableExtension _ _).2 inferInstance
  have : IsAdicComplete (maximalIdeal K) K := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  exact corollaire3_10 (formallySmoothNAdic_of_formallySmooth' (maximalIdeal K))

end Grothendieck.Folder22CohenAlgebras

#print axioms Grothendieck.Folder22CohenAlgebras.corollaire3_13
#print axioms Grothendieck.Folder22CohenAlgebras.corollaire3_9
#print axioms Grothendieck.Folder22CohenAlgebras.question1
#print axioms Grothendieck.Folder22CohenAlgebras.isRegularLocalRing_of_formallySmoothNAdic
#print axioms Grothendieck.Folder22CohenAlgebras.corollaire3_10
#print axioms Grothendieck.Folder22CohenAlgebras.corollaire3_12_existence
