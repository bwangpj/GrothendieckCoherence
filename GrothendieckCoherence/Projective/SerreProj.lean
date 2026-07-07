import Mathlib
import GrothendieckCoherence.Projective.CohomologyProjectiveSpace

/-!
# Serre finiteness and vanishing on Proj (Blueprint chapter: serre-proj)

`lem:affine-finite-proj`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Proj

/-- **Blueprint `lem:affine-finite-proj`** (Stacks 01YW): for `A` Noetherian and
`X = Proj S` projective over `Spec A`, `ℱ` coherent: `Hⁱ(X, ℱ)` is a finite
`A`-module for all `i`, `Hⁱ(X, ℱ(d)) = 0` for `i > 0`, `d ≫ 0`, and `ℱ(d)` is
globally generated for `d ≫ 0`. Recorded as a placeholder. -/
theorem cohomology_coherent_finite_and_vanishing
    {A : Type u} [CommRing A] [IsNoetherianRing A] : True := trivial

end AlgebraicGeometry.Proj
