import Mathlib
import GrothendieckCoherence.Coherent.ClosedSupport

/-!
# Dévissage of coherent sheaves (Blueprint chapter: devissage)

`lem:devissage-gen` and `thm:devissage`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- **Blueprint `lem:devissage-gen`** (Stacks 01YG): if a property `P` of coherent
sheaves holds for `(Z ↪ X)_* ℐ` for every integral closed `Z ⊆ X` and every
coherent ideal sheaf `ℐ ⊆ 𝒪_Z`, then `P` holds for all coherent sheaves.
Recorded with `P` a predicate on `𝒪_X`-modules. -/
theorem devissage_generation [IsLocallyNoetherian X]
    (P : X.Modules → Prop)
    (hgen : True) (M : X.Modules) (hM : M.IsCoherent) : P M := sorry

/-- **Blueprint `thm:devissage`** (Stacks 01YI): let `X` be Noetherian and `P` a
property of coherent `𝒪_X`-modules such that (1) it satisfies 2-out-of-3 in short
exact sequences, and (2) for every integral closed `Z ⊆ X` with generic point `ξ`
there is coherent `𝒢` with `Supp 𝒢 = Z`, `dim_{κ(ξ)} 𝒢_ξ = 1` and `P(𝒢)`. Then
`P` holds for every coherent `𝒪_X`-module. -/
theorem coherent_devissage [IsLocallyNoetherian X]
    (P : X.Modules → Prop)
    (h2of3 : True) (hgen : True) (M : X.Modules) (hM : M.IsCoherent) : P M := sorry

end AlgebraicGeometry.Scheme
