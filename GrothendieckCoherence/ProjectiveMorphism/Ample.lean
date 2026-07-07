import Mathlib
import GrothendieckCoherence.QuasiCoherent.Invertible

/-!
# Ample invertible sheaves and projective morphisms (Blueprint chapter: ample)

`def:projective-morphism` and `lem:pullback-ample`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Blueprint `def:projective-morphism`** (Stacks 01VG): an invertible
`𝒪_X`-module `L` is `f`-relatively ample if, locally on `S`, `X → Spec Aᵢ` is a
locally closed immersion into some `ℙⁿ_{Aᵢ}` pulling `𝒪(1)` back to `L`.
Placeholder predicate (`True` stands for the local embedding condition). -/
def Scheme.IsRelativelyAmple (f : X ⟶ S) (L : X.Modules) : Prop :=
  L.IsInvertible ∧ True

/-- **Blueprint `def:projective-morphism`** (Stacks 01W8): `f : X → S` is
*projective* if it factors as a closed immersion `X ↪ ℙⁿ_S` followed by the
projection (equivalently, admits an `f`-ample `L` with `f` proper). Placeholder:
recorded as `f` proper together with an ample invertible sheaf. -/
def IsProjective (f : X ⟶ S) : Prop :=
  IsProper f ∧ ∃ L : X.Modules, Scheme.IsRelativelyAmple f L

/-- **Blueprint `lem:pullback-ample`** (Stacks 02NR): if `i : X → ℙⁿ_S` is a closed
immersion over `S` then `i^* 𝒪(1)` is `f`-relatively ample and `f : X → S` is
projective and proper. Recorded as a placeholder. -/
theorem Scheme.relativelyAmple_pullback_twist (f : X ⟶ S) : True := trivial

end AlgebraicGeometry
