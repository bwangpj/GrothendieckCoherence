import Mathlib
import GrothendieckCoherence.Coherent.Basic
import GrothendieckCoherence.Cohomology.Basic

/-!
# Closed immersions and support (Blueprint chapter: closed-support)

`lem:closed-immersion-acyclic` and `lem:support`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}}

/-- **Blueprint `lem:closed-immersion-acyclic`** (Stacks 01Y6): for a closed
immersion `i : Z → X` of locally Noetherian schemes and coherent `𝒢` on `Z`,
`i_* 𝒢` is coherent, `i_*` is exact, and `Rᵖ i_* 𝒢 = 0` for all `p > 0`.
Recorded as: coherence of `i_* 𝒢` and higher vanishing. -/
theorem closedImmersion_pushforward_coherent_and_acyclic
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (G : Z.Modules) (hG : G.IsCoherent) :
    (((Modules.pushforward i).obj G).IsCoherent) ∧
      ∀ p, 0 < p → IsZero ((higherDirectImage i p).obj G) := sorry

/-- **Blueprint `lem:support`** (Stacks 01YB): for coherent `ℱ` on a Noetherian
scheme, `Supp ℱ` is closed; on an integral closed `Z` with generic point `ξ`,
`𝒪_{X,ξ} = κ(ξ)` is a field and any coherent `𝒢` supported on `Z` has `𝒢_ξ` a
finite-dimensional `κ(ξ)`-vector space. Recorded as placeholders. -/
theorem Modules.support_closed [IsLocallyNoetherian X] (M : X.Modules)
    (hM : M.IsCoherent) : True := trivial

theorem Modules.genericStalk_finrank [IsLocallyNoetherian X] (M : X.Modules)
    (hM : M.IsCoherent) : True := trivial

end AlgebraicGeometry.Scheme
