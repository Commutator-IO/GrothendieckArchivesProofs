/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

/-!
# Folder 126: generic descent data, not stated

The open row `126-generic-descent` of the edition's list of findings
(`src/content/findings.ts`), folder 126, pp. 26–29. It cannot be stated faithfully with Mathlib
and the Stacks library; what is missing.

* `126-generic-descent`: for `S` noetherian, `T → S` flat of finite type and a fibred category
  `F` on finite-type `S`-schemes for which flat surjections are of `F`-descent (full faithfulness
  only), an isomorphism `φ : p₁^*X ≅ p₂^*X` defined over a dense open of `T ×_S T` and satisfying
  the cocycle condition over a dense open of `T ×_S T ×_S T` extends, after shrinking `T` to a
  dense open, to a genuine descent datum agreeing with `φ` where both are defined. Status:
  candidate (closest in print: Weil 1956, Th. 6–7, over a field and for quasi-projective
  varieties). Missing: descent data defined only on dense opens of the fibre products, with the
  cocycle condition compared on a dense open of the triple product through the coherence
  isomorphisms of the fibred category. The Stacks library has descent data for covering sieves
  (`CategoryTheory.Functor.SieveDescentDatum`, Stacks 026B) and for pullbacks (Stacks 02ZD),
  always over the whole fibre products; « of `F`-descent » in the sense of full faithfulness only
  would also have to be written. The argument is the edition's reordering of a page the reading
  calls circular, and its step « sauf erreur » (surjectivity of `W' → W ×_{T×T} W`) is unproved.
-/
