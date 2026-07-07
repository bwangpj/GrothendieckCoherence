import Mathlib
import GrothendieckCoherence.Cech.Complex
import GrothendieckCoherence.QuasiCoherent.Basic

/-!
# Vanishing on affines and the comparison (Blueprint chapter: affine-vanishing)

`thm:affine-vanishing` (Serre) and `cor:affine-cover-computes`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Blueprint `thm:affine-vanishing`** (Serre; Stacks 01XB): if `X = Spec R` is
affine and `ℱ` is quasi-coherent, then `Hⁱ(X, ℱ) = 0` for all `i > 0`. -/
theorem cohomology_qcoh_affine_eq_zero (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) (hM : M.IsQuasicoherent) (i : ℕ) (hi : 0 < i) :
    IsZero ((Scheme.cohomology X i).obj M) := sorry

/-- **Blueprint `cor:affine-cover-computes`** (Stacks 01X9): on a separated scheme
(so intersections of affine opens are affine), an affine open cover computes
cohomology: `Ȟ^p(𝒰, ℱ) ≅ H^p(X, ℱ)`. The separatedness hypothesis is recorded as
`hsep` pending the scheme-level `IsSeparated` API. -/
noncomputable def Scheme.cechCohomology_iso_cohomology_of_separated
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hsep : True)
    (M : X.Modules) (hM : M.IsQuasicoherent) (p : ℕ) :
    Scheme.cechCohomology U M p ≅ (Scheme.cohomology X p).obj M := sorry

end AlgebraicGeometry
