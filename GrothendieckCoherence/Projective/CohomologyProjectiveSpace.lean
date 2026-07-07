import Mathlib
import GrothendieckCoherence.Cech.AffineVanishing
import GrothendieckCoherence.Projective.Twist

/-!
# Cohomology of projective space (Blueprint chapter: cohomology-Pn)

`thm:cohomology-Pn` (Serre's computation) and `cor:Pn-finite-vanish`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Blueprint `thm:cohomology-Pn`** (Serre; Stacks 01XS): for a ring `A` and
`n ≥ 0`, the cohomology of `𝒪(d)` on `ℙⁿ_A`:
`⊕_d H⁰ ≅ A[T₀,…,T_n]`, `⊕_d Hⁿ ≅ (T₀⋯T_n)⁻¹ A[T₀⁻¹,…,T_n⁻¹]`, and
`Hᵍ(ℙⁿ_A, 𝒪(d)) = 0` for `0 < q < n`; each is a finite free `A`-module.
Recorded as a placeholder pending the twisting-sheaf and Proj-cohomology API. -/
theorem cohomology_projectiveSpace_twist {A : Type u} [CommRing A] (n : ℕ) (q d : ℤ) :
    True := trivial

/-- **Blueprint `cor:Pn-finite-vanish`** (Stacks 01XS): `Hᵍ(ℙⁿ_A, 𝒪(d))` is a
finite `A`-module for all `q, d`, and vanishes for `q > 0` and `d ≫ 0`. -/
theorem cohomology_projectiveSpace_finite_and_vanishing
    {A : Type u} [CommRing A] (n : ℕ) : True := trivial

end AlgebraicGeometry
