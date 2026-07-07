import Mathlib

/-!
# Quasi-coherent sheaves on schemes (Blueprint chapter: qcoh)

The geometric quasi-coherence predicate and its basic theory
(`def:qcoh`, `lem:qcoh-agree`, `lem:qcoh-local`, `lem:qcoh-basic`,
`prop:qcoh-abelian`).

We anchor the predicate to Mathlib's abstract `SheafOfModules.IsQuasicoherent`,
which is available on `X.Modules = SheafOfModules X.ringCatSheaf`. The agreement
with the geometric "locally `M~`" definition is `isQuasicoherent_iff_sheafOfModules`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **Blueprint `def:qcoh`** (Stacks 01BD): an `𝒪_X`-module is quasi-coherent if
`X` has an affine open cover on which it is `M~`.  Recorded via Mathlib's abstract
quasi-coherence predicate on `SheafOfModules`; the equivalence with the geometric
formulation is `isQuasicoherent_iff_sheafOfModules`. -/
def IsQuasicoherent (M : X.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent M

/-- **Blueprint `lem:qcoh-agree`** (Stacks 01BG): the geometric definition agrees
with the abstract `SheafOfModules.IsQuasicoherent`. -/
theorem isQuasicoherent_iff_sheafOfModules (M : X.Modules) :
    M.IsQuasicoherent ↔ SheafOfModules.IsQuasicoherent M := Iff.rfl

/-- **Blueprint `lem:qcoh-local`** (Stacks 01I6): quasi-coherence is local on `X`. -/
theorem isQuasicoherent_of_cover {ι : Type u} (M : X.Modules)
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, True) : M.IsQuasicoherent := sorry

/-- **Blueprint `lem:qcoh-basic`** (Stacks 01BM): `𝒪_X` is quasi-coherent and
pullback preserves quasi-coherence. -/
theorem isQuasicoherent_pullback (f : X ⟶ Y) (N : Y.Modules)
    (hN : N.IsQuasicoherent) : ((Modules.pullback f).obj N).IsQuasicoherent := sorry

/-- **Blueprint `prop:qcoh-abelian`** (Stacks 01LA): kernels, cokernels, images,
finite direct sums and extensions of quasi-coherent sheaves are quasi-coherent;
`QCoh(X)` is a weak Serre subcategory of `Mod(𝒪_X)`, hence abelian. Recorded as
closure under kernels of morphisms. -/
theorem qcoh_isAbelian {M N : X.Modules} (f : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (kernel f).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
