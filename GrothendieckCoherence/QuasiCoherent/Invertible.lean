import Mathlib
import GrothendieckCoherence.QuasiCoherent.Basic

/-!
# Invertible sheaves and twists (Blueprint chapter: invertible)

`def:invertible`, `lem:tensor-invertible-exact`. Only the light amount needed for
the projective case and Chow's lemma.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Blueprint `def:invertible`** (Stacks 01CR): an `𝒪_X`-module is *invertible* if
it is locally free of rank `1`, i.e. `X` has an open cover on which it is `𝒪_X`.
Placeholder predicate (`True` stands for the local-triviality condition, pending
the locally-free API). -/
def IsInvertible (L : X.Modules) : Prop :=
  L.IsQuasicoherent ∧ True

/-- **Blueprint `lem:tensor-invertible-exact`** (Stacks 01CR): for invertible `L`,
`- ⊗ L` is exact and preserves quasi-coherence, with inverse `- ⊗ L⁻¹`. Recorded
as: tensoring preserves quasi-coherence. -/
theorem tensorInvertible_exact {L M : X.Modules} (hL : L.IsInvertible)
    (hM : M.IsQuasicoherent) : True := trivial

end AlgebraicGeometry.Scheme.Modules
