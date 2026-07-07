import Mathlib
import GrothendieckCoherence.Cech.AffineVanishing

/-!
# Higher direct images of quasi-coherent sheaves (Blueprint chapter: hdi-qcoh)

`prop:hdi-qcoh` and `prop:hdi-affine-base`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- **Blueprint `prop:hdi-qcoh`** (Stacks 01XJ): if `f` is quasi-compact and
quasi-separated and `ℱ` is quasi-coherent, then `Rⁱ f_* ℱ` is quasi-coherent for
all `i ≥ 0`. -/
theorem higherDirectImage_isQuasicoherent (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) (hM : M.IsQuasicoherent) (i : ℕ) :
    ((higherDirectImage f i).obj M).IsQuasicoherent := sorry

/-- **Blueprint `prop:hdi-affine-base`** (Stacks 01XK): for `f : X → Spec A`
quasi-compact quasi-separated with `ℱ` quasi-coherent,
`Rⁱ f_* ℱ ≅ (Hⁱ(X, ℱ))~`; in particular `Rⁱ f_* ℱ` is coherent iff `Hⁱ(X, ℱ)` is
a finite `A`-module. Recorded as the quasi-coherence conclusion. -/
theorem higherDirectImage_over_affine {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) (hM : M.IsQuasicoherent) (i : ℕ) :
    ((higherDirectImage f i).obj M).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme
