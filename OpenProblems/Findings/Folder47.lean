/-!
# Folder 47: the Fourier transform on the Chow ring of an abelian scheme, not stated

The open row `47-chow-fourier-todd-over-base` of the edition's list of findings
(`src/content/findings.ts`), folder 47, pp. 9–10. It cannot be stated faithfully with Mathlib
and the Stacks library; what is missing.

* `47-chow-fourier-todd-over-base`: over a base `S`, Grothendieck–Riemann–Roch for `m_A` and
  `pr_2` gives `ch(x * y) = (ch x * ch y) · Todd(t_A)` on an abelian scheme `A`, the transform
  `Ψ_D = pr_{2*}(pr_1^*(−) · exp D)` turns the Pontryagin product into the product with no
  correction, and the cup-to-Pontryagin formula acquires a factor pulled back from `S`. Status:
  candidate; to compare with Deninger–Murre (1991) § 2 and Künnemann. Missing: the Todd class and
  Grothendieck–Riemann–Roch (the Stacks library has Chow groups, Chern classes and the Chern
  character on `K₀`,
  `AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative`, Stacks 0FEM,
  but no Todd class and no GRR), proper pushforward on rational Chow groups of an
  abelian scheme over a base with its Pontryagin product, and the tangent bundle `t_A` and
  `ω_A` of an abelian scheme. The factor itself is disputed: the reading replaces the page's `T`
  by `Todd(t_A) · Todd(t_B) · ch(ω_A)`, and the pass's own conditional step would make it `1`.
-/
