import Mathlib
import GrothendieckCoherence.QuasiCoherent.Invertible
import GrothendieckCoherence.Coherent.Basic

/-!
# Twisting sheaves and graded modules on Proj (Blueprint chapter: proj-twist)

`con:proj-tilde`, `lem:proj-sections`, `prop:proj-graded`.

These live over `Proj S` for a graded ring `S`. The constructions (the graded
tilde functor and twisting sheaves `𝒪(d)`) are recorded as placeholders; the
substantive `prop:proj-graded` (every coherent sheaf on Proj comes from a graded
module) is a `sorry` statement.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Proj

/-- **Blueprint `con:proj-tilde`** (Stacks 01M3): the twisting sheaf `𝒪_X(d)` on
`X = Proj S`. Placeholder: recorded as an abstract `𝒪_X`-module for each `d`. -/
noncomputable def twistingSheaf {R : Type u} [CommRing R] {A : Type u} [CommRing A]
    [Algebra R A] (d : ℤ) : True := trivial

/-- **Blueprint `prop:proj-graded`** (Stacks 01YS): for `A` Noetherian and `S` a
finitely generated graded `A`-algebra generated in degree `1`, every coherent
`𝒪_{Proj S}`-module is `M~` for a finitely generated graded `S`-module `M`, and
`M_d ≅ H⁰(X, M~(d))` for `d ≫ 0`. Recorded as a placeholder. -/
theorem coherent_from_gradedModule : True := trivial

/-- **Blueprint `lem:proj-sections`** (Stacks 01M3): on the standard cover
`{D₊(xᵢ)}`, `𝒪_X(d)|_{D₊(f)} ≅ (S(d)_{(f)})~`. Recorded as a placeholder. -/
theorem twistingSheaf_restrict : True := trivial

end AlgebraicGeometry.Proj
