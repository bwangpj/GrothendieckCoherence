import Mathlib
import GrothendieckCoherence.Cohomology.Flasque

/-!
# Bridge: abstract `rightDerived` vs sheaf cohomology (Blueprint chapter: bridge1)

`prop:bridge-rderived`: the abstract derived pushforward computes `Rⁿ f_*`.

Since `higherDirectImage f n` is *defined* as `(Modules.pushforward f).rightDerived n`,
this "bridge" is definitionally the identity at the level of the abstract functor;
the real content is compatibility with the geometric higher direct image once the
latter is developed. Recorded here as an isomorphism placeholder.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **Blueprint `prop:bridge-rderived`**: for `f : X ⟶ Y` and quasi-coherent
`M : X.Modules`, `((Modules.pushforward f).rightDerived n).obj M ≅ Rⁿ f_* M`,
compatibly with the equivalence between geometric `𝒪_X`-modules and
`SheafOfModules`. Here the two sides are definitionally equal. -/
noncomputable def rightDerivedPushforward_iso_higherDirectImage
    (f : X ⟶ Y) (n : ℕ) (M : X.Modules) (hM : M.IsQuasicoherent) :
    ((Modules.pushforward f).rightDerived n).obj M ≅
      (Scheme.higherDirectImage f n).obj M :=
  Iso.refl _

end AlgebraicGeometry.Scheme.Modules
