import Mathlib
import GrothendieckCoherence.Finiteness
import GrothendieckCoherence.Cohomology.Bridge
import GrothendieckCoherence.Coherent.Basic

/-!
# From coherence to finite presentation (Blueprint chapter: conclude)

`thm:target-final` = `thm:goal`: the target Lean statement of the whole project.

Proof strategy (blueprint): `f` proper ⇒ of finite type ⇒ `X` locally Noetherian
(`locallyNoetherian_of_finiteType`); `M` finitely presented ⇒ coherent
(`isFinitePresentation_iff_isCoherent`); the derived object is `Rⁿ f_* M`
(`rightDerivedPushforward_iso_higherDirectImage`), coherent by
`higherDirectImage_coherent_of_isProper`; back to finite presentation on the
locally Noetherian base `Y`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **Grothendieck's Coherence Theorem** (EGA III, Théorème 3.2.1; Stacks 02O5),
target form: for a proper `f : X ⟶ Y` with `Y` locally Noetherian and `M` a sheaf
of modules of finite presentation on `X`, the object
`((Modules.pushforward f).rightDerived n).obj M` is of finite presentation for
every `n`. -/
theorem rightDerivedPushforward_isFinitePresentation_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (M : X.Modules) [SheafOfModules.IsFinitePresentation M] (n : ℕ) :
    SheafOfModules.IsFinitePresentation (((Modules.pushforward f).rightDerived n).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
