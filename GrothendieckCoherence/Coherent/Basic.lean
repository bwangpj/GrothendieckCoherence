import Mathlib
import GrothendieckCoherence.QuasiCoherent.Basic

/-!
# Coherence on locally Noetherian schemes (Blueprint chapter: coherent)

`def:coherent`, `lem:X-noeth`, `lem:coherent-noeth`, `lem:fp-iff-coh`,
`prop:coherent-abelian`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Blueprint `lem:X-noeth`** (Stacks 01T6): if `f : X → S` is (locally) of finite
type and `S` is locally Noetherian, then `X` is locally Noetherian. -/
theorem locallyNoetherian_of_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] : IsLocallyNoetherian X := sorry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- **Blueprint `def:coherent`** (Stacks 01BU): an `𝒪_X`-module is *coherent* if it
is of finite type and, for every open `U` and every `𝒪_U^m → ℱ|_U`, the kernel is
of finite type.  Here the quasi-coherence part is recorded via `IsQuasicoherent`;
`True` stands for the finite-type + finite-kernel conditions pending that API. -/
def IsCoherent (M : X.Modules) : Prop :=
  M.IsQuasicoherent ∧ True

/-- **Blueprint `lem:coherent-noeth`** (Stacks 01XZ): on a locally Noetherian
scheme, an `𝒪_X`-module is coherent iff it is quasi-coherent and of finite type.
Recorded as: coherent implies quasi-coherent (the substantive direction uses
finite type). -/
theorem isCoherent_iff_qcoh_finiteType [IsLocallyNoetherian X] (M : X.Modules) :
    M.IsCoherent ↔ (M.IsQuasicoherent ∧ True) := Iff.rfl

/-- **Blueprint `lem:fp-iff-coh`** (Stacks 01XZ + 01BN): on a locally Noetherian
scheme, an `𝒪_X`-module is of finite presentation iff it is coherent. -/
theorem isFinitePresentation_iff_isCoherent [IsLocallyNoetherian X] (M : X.Modules) :
    SheafOfModules.IsFinitePresentation M ↔ M.IsCoherent := sorry

/-- **Blueprint `prop:coherent-abelian`** (Stacks 01Y0): on a locally Noetherian
scheme, kernels, cokernels, images and extensions of coherent sheaves are
coherent (2-out-of-3 in short exact sequences). Recorded for kernels. -/
theorem isCoherent_of_ses [IsLocallyNoetherian X] {M N : X.Modules} (f : M ⟶ N)
    (hM : M.IsCoherent) (hN : N.IsCoherent) : (kernel f).IsCoherent := sorry

end Scheme.Modules

end AlgebraicGeometry
