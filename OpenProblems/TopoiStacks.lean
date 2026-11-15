/-!
# Topoi and stacks: the open problems, not stated

Section « Topoi and stacks » of the note on the open problems of the Montpellier notes
(`docs/problems/article.tex`): problems p:noncoh, p:fol, p:pic, p:domram. None of them can be
stated faithfully with Mathlib and the Stacks library; for each, what is missing.

* p:noncoh (folder 161-2, pp. 39, 41–42, *Algèbre universelle*, [c. 1963–1973]): the classifying
  topoi of the geometric theories of rings with irreducible spectrum and of rings with
  zero-dimensional spectrum are not coherent; do they have enough points? Status: open (nothing
  found in Johnstone or Caramello). Missing: geometric theories and their classifying topoi,
  coherent topoi, and points of a topos. The Stacks library has morphisms of topoi
  (`MorphismOfTopoi`), not these.
* p:fol (folder 119, pp. 144–145, March 1986): an equivalence between spaces with a local
  equivalence relation (locally open, locally connected fibres) and locally open geometric
  morphisms with locally connected fibres from `Top(X)` to a « multiplicité topologique ».
  Status: open (the functors are in SGA 4 IV 9.8.3 and in Kock and Moerdijk; no equivalence
  found). Missing: local equivalence relations on spaces, their quotient topoi, locally open and
  locally connected geometric morphisms, étendues; and the page's third condition is partly
  illegible.
* p:pic (folder 134-1, p. 5, letter to Deligne, 27 August 1974; withdrawn in part in a letter to
  Breen of 5 February 1975): is every homomorphism `M → ₂N` of abelian sheaves on a topos the
  symmetry invariant of a Picard stack pinned by `M` and `N`? Status: open; the 1974 « universal »
  argument rests on a miscalculation by the 1975 letter's account. Missing: stacks over a topos,
  Picard stacks and their symmetry invariant, and `Ext³` of abelian sheaves on a topos as the home
  of the obstruction (Mathlib has `Ext` in abelian categories, but not the Picard-stack side).
* p:domram (folder 29, p. 197, *Groupe fondamental*, 1959–1969): morphisms of « domaines de
  ramification » (stacks of multigaloisian categories over the étale site with a geometric
  realisation, axioms R1, R2) are fully faithful. Status: open (Proposition 6 of the page, without
  proof; nothing found). Missing: stacks of categories over the étale site, multigaloisian
  categories, and the axioms R1–R2 themselves, which the edition has not verified.
-/
