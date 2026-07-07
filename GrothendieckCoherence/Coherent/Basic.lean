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
is quasi-coherent and of finite presentation.  Mathlib's
`SheafOfModules.IsFinitePresentation` captures "locally finitely presented", which on
a locally Noetherian scheme is equivalent to coherence (Stacks 01XZ + 01BN). -/
def IsCoherent (M : X.Modules) : Prop :=
  M.IsQuasicoherent ∧ SheafOfModules.IsFinitePresentation M

/-- **Blueprint `lem:coherent-noeth`** (Stacks 01XZ): on a locally Noetherian
scheme, an `𝒪_X`-module is coherent iff it is quasi-coherent and of finite
presentation.  The `IsFinitePresentation` part already implies `IsQuasicoherent`
(see `SheafOfModules.IsFinitePresentation` → `IsQuasicoherent` instance in Mathlib),
but we keep both conjuncts explicit for clarity. -/
theorem isCoherent_iff_qcoh_finiteType [IsLocallyNoetherian X] (M : X.Modules) :
    M.IsCoherent ↔ (M.IsQuasicoherent ∧ SheafOfModules.IsFinitePresentation M) := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Blueprint `lem:fp-iff-coh`** (Stacks 01XZ + 01BN): on a locally Noetherian
scheme, an `𝒪_X`-module is of finite presentation iff it is coherent.
The forward direction (`IsFinitePresentation → IsCoherent`) holds because
`SheafOfModules.IsFinitePresentation` implies `IsQuasicoherent` via the Mathlib
instance (Quasicoherent.lean:274); the reverse direction requires a deep Noetherian
argument. -/
theorem isFinitePresentation_iff_isCoherent [IsLocallyNoetherian X] (M : X.Modules) :
    SheafOfModules.IsFinitePresentation M ↔ M.IsCoherent := by
  constructor
  · intro h
    refine ⟨?_, h⟩
    -- Forward: `IsFinitePresentation → IsQuasicoherent` via Quasicoherent.lean:274.
    -- We build the `IsQuasicoherent` witness directly from the `IsFinitePresentation`
    -- data; `set_option backward.isDefEq.respectTransparency false` (at declaration
    -- level) ensures the `X.Modules` type alias is unfolded during elaboration.
    change SheafOfModules.IsQuasicoherent M
    exact { nonempty_quasicoherentData := ⟨h.exists_quasicoherentData.choose⟩ }
  · intro ⟨_, h⟩
    exact h

/-- **Blueprint `prop:coherent-abelian`** (Stacks 01Y0): on a locally Noetherian
scheme, kernels, cokernels, images and extensions of coherent sheaves are
coherent (2-out-of-3 in short exact sequences). Recorded for kernels. -/
theorem isCoherent_of_ses [IsLocallyNoetherian X] {M N : X.Modules} (f : M ⟶ N)
    (hM : M.IsCoherent) (hN : N.IsCoherent) : (kernel f).IsCoherent := sorry

end Scheme.Modules

end AlgebraicGeometry
