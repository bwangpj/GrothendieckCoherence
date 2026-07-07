import Mathlib
import GrothendieckCoherence.ProjectiveMorphism.Ample

/-!
# Chow's lemma (Blueprint chapter: chow)

`thm:chow` and `rem:chow-graph`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Blueprint `thm:chow`** (Stacks 0200; EGA II 5.6.1): let `S` be Noetherian and
`f : X → S` separated of finite type. Then there exist `n`, a proper surjective
`π : X' → X` that is an isomorphism over a dense open `U ⊆ X`, and an immersion
`X' ↪ ℙⁿ_S` over `S`. If `f` is proper then `X' → S` is projective. Recorded as an
existence statement with placeholders for the geometric data. -/
theorem chowLemma (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X), True := sorry

/-- **Blueprint `rem:chow-graph`** (Stacks 0201): the graph `(i, π) : X' → ℙᵐ_X`
is a closed immersion, so `L := i^* 𝒪(1)` is `π`-relatively ample; and `X' → S` is
projective. Recorded as a placeholder. -/
theorem chowLemma_graph_closedImmersion (f : X ⟶ S) : True := trivial

end AlgebraicGeometry
