module

public import Grothendieck.Folder55LemmaB
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.Algebra.Category.Ring.Limits
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 55, page 13: the structure sheaf of the counterexample, as a sheaf of rings

`Grothendieck.Folder55LemmaB.O` is a subsheaf of the sheaf of all functions; this file makes it
a sheaf of rings on `Xsp`, `Grothendieck.Folder55LemmaB.Osheaf`, the input of the coherence
statements of `Grothendieck/Folder55Coherent.lean`. The ring data `κ`, `ε`, `ι` stay abstract.
-/

open CategoryTheory TopologicalSpace Opposite

namespace Grothendieck.Folder55LemmaB
open Pt

variable {k D K : Type} [CommRing k] [CommRing D] [CommRing K] (κ : k →+* D) (ε : D →+* k)
  (ι : D →+* K)

theorem O_zero_mem (U : Opens Xsp) : (0 : Sec k D K U) ∈ (O κ ε ι).sections U := by
  refine ⟨fun _ _ => ⟨?_, ?_, rfl⟩, fun _ _ => ?_, fun _ => ⟨0, fun y _ => ?_⟩⟩
  · exact map_zero ι
  · exact map_zero ι
  · show ι (κ (0 : k)) = (0 : K)
    rw [map_zero, map_zero]
  · exact (map_zero (constHom κ ι y.1)).symm

theorem O_neg_mem {U : Opens Xsp} {s : Sec k D K U} (hs : s ∈ (O κ ε ι).sections U) :
    -s ∈ (O κ ε ι).sections U := by
  obtain ⟨hsC, hsE, hsI⟩ := hs
  refine ⟨fun n h => ?_, fun n h => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hsC n h
    refine ⟨?_, ?_, ?_⟩
    · show ι (-atC s h).1 = -atO s (mem_o_of_c h)
      rw [Prod.fst_neg, map_neg, h1]
    · show ι (-atC s h).2 = -atD s (mem_d_of_c h)
      rw [Prod.snd_neg, map_neg, h2]
    · show ε (-atC s h).1 = ε (-atC s h).2
      rw [Prod.fst_neg, Prod.snd_neg, map_neg, map_neg, h3]
  · show ι (κ (-atE s h)) = -atO s (mem_o_of_e h)
    rw [map_neg, map_neg, hsE n h]
  · obtain ⟨N, hN⟩ := hsI h
    refine ⟨N, fun y hy => ?_⟩
    show -s y = constHom κ ι y.1 (-atInf s h)
    rw [map_neg, hN y hy]

/-- The sections of `𝒪` over `U`, as a subring of all the functions. -/
def Osubring (U : Opens Xsp) : Subring (Sec k D K U) where
  carrier := (O κ ε ι).sections U
  one_mem' := O_one_mem κ ε ι U
  mul_mem' := O_mul_mem κ ε ι
  zero_mem' := O_zero_mem κ ε ι U
  add_mem' := O_add_mem κ ε ι
  neg_mem' := O_neg_mem κ ε ι

/-- `𝒪` as a local predicate on functions. -/
def Olp : TopCat.LocalPredicate (fun x : Xsp => Val k D K x) where
  pred {U} f := f ∈ (O κ ε ι).sections U
  res {U V} i f h := (O κ ε ι).restrict i.le h
  locality {U} f h := (O κ ε ι).isLocal U f fun x hx => by
    obtain ⟨V, hxV, i, hV⟩ := h ⟨x, hx⟩
    exact ⟨V, i.le, hxV, hV⟩

/-- **The structure sheaf `𝒪`, as a presheaf of rings.** -/
def Opre : TopCat.Presheaf RingCat Xsp where
  obj U := RingCat.of (Osubring κ ε ι U.unop)
  map i := RingCat.ofHom
    { toFun := fun s => ⟨fun x => s.1 ⟨x.1, i.unop.le x.2⟩, (O κ ε ι).restrict i.unop.le s.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

@[montpellier "55, 13"]
theorem Opre_isSheaf : (Opre κ ε ι).IsSheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget RingCat) _).2 ?_
  refine TopCat.Presheaf.isSheaf_of_iso ?_ (TopCat.subpresheafToTypes.isSheaf (Olp κ ε ι))
  exact NatIso.ofComponents (fun U => Iso.refl _) (fun _ => rfl)

/-- **The structure sheaf `𝒪` of the counterexample, as a sheaf of rings.** -/
@[montpellier "55, 13"]
def Osheaf : Sheaf (Opens.grothendieckTopology Xsp) RingCat := ⟨Opre κ ε ι, Opre_isSheaf κ ε ι⟩

end Grothendieck.Folder55LemmaB
