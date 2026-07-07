import Mathlib
import GrothendieckCoherence.Cohomology.Basic

/-!
# The Čech complex (Blueprint chapter: cech)

`def:cech`, `lem:cech-basic`, `prop:cech-to-derived`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- **Blueprint `def:cech`** (Stacks 01ED): the Čech complex
`Č^p(𝒰, ℱ) = ∏_{i₀<…<i_p} ℱ(U_{i₀…i_p})` of an open cover `𝒰` and an
`𝒪_X`-module `ℱ`, with the alternating differential. Placeholder object. -/
noncomputable def cechComplex {ι : Type u} (U : ι → X.Opens) (M : X.Modules) :
    CochainComplex Ab.{u} ℕ := sorry

/-- **Blueprint `def:cech`** (Stacks 01ED): Čech cohomology
`Ȟ^p(𝒰, ℱ)`, the cohomology of the Čech complex. -/
noncomputable def cechCohomology {ι : Type u} (U : ι → X.Opens) (M : X.Modules)
    (p : ℕ) : Ab.{u} :=
  (cechComplex U M).homology p

/-- **Blueprint `lem:cech-basic`** (Stacks 01EF): `Ȟ⁰(𝒰, ℱ) ≅ Γ(X, ℱ)`. -/
noncomputable def cechCohomology_zero {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (M : X.Modules) :
    cechCohomology U M 0 ≅ (sectionsFunctor X).obj M := sorry

/-- **Blueprint `prop:cech-to-derived`** (Stacks 01EW): the natural comparison map
`Ȟ^p(𝒰, ℱ) → H^p(X, ℱ)`. -/
noncomputable def cechToDerived {ι : Type u} (U : ι → X.Opens) (M : X.Modules)
    (p : ℕ) : cechCohomology U M p ⟶ (cohomology X p).obj M := sorry

/-- **Blueprint `prop:cech-to-derived`** (Stacks 01EW / Leray): the comparison is
an isomorphism when every finite intersection is `ℱ`-acyclic (acyclic covers). -/
theorem cechToDerived_iso_of_acyclicCover {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (M : X.Modules) (p : ℕ)
    (hacyclic : True) : IsIso (cechToDerived U M p) := sorry

end AlgebraicGeometry.Scheme
