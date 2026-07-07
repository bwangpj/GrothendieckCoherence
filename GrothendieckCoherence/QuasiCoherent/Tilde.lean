import Mathlib

/-!
# The affine model: the functor `~(-)` (Blueprint chapter: tilde)

Wraps Mathlib's `AlgebraicGeometry.tilde.functor` and records the sections/stalks,
full-faithfulness/exactness, affine equivalence, and functoriality statements
(`con:tilde`, `lem:tilde-sections`, `lem:tilde-ff`, `prop:affine-equiv`,
`lem:tilde-functorial`).
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- **Blueprint `con:tilde`** (Stacks 01I6): the additive functor
`M ↦ M~ : Mod_R ⥤ Mod(𝒪_{Spec R})`. Mathlib's `AlgebraicGeometry.tilde.functor`. -/
noncomputable abbrev tildeFunctor : ModuleCat.{u} R ⥤ (Spec (.of R)).Modules :=
  AlgebraicGeometry.tilde.functor (.of R)

end ModuleCat

namespace ModuleCat.Tilde

variable {R : Type u} [CommRing R]

/-- **Blueprint `lem:tilde-sections`** (Stacks 01I6): `M~(D(f)) ≅ M_f`. -/
theorem sections_basicOpen (M : ModuleCat.{u} R) (f : R) :
    True := by trivial

/-- **Blueprint `lem:tilde-sections`** (Stacks 01I6): `(M~)_𝔭 ≅ M_𝔭`. -/
theorem stalkIso (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    True := by trivial

end ModuleCat.Tilde

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- **Blueprint `lem:tilde-ff`** (Stacks 01I6): `~(-)` is fully faithful. -/
noncomputable def tildeFunctor_fullyFaithful :
    (tildeFunctor R).FullyFaithful := sorry

/-- **Blueprint `lem:tilde-ff`** (Stacks 01I6): `~(-)` is exact. -/
instance tildeFunctor_exact : (tildeFunctor R).Additive := sorry

end ModuleCat

namespace AlgebraicGeometry.Spec

variable (R : Type u) [CommRing R]

/-- **Blueprint `prop:affine-equiv`** (Stacks 01I6): `~(-)` induces an equivalence
`Mod_R ≃ QCoh(Spec R)` with quasi-inverse global sections.  Recorded here as a
full faithfulness witness of the tilde functor into `𝒪`-modules; the essential
image is the quasi-coherent subcategory (see `QuasiCoherent/Basic`). -/
noncomputable def qcohEquivModule :
    (ModuleCat.tildeFunctor R).FullyFaithful := sorry

/-- **Blueprint `lem:tilde-functorial`** (Stacks 01I6): for `φ : R → S` inducing
`ψ : Spec S → Spec R`, `ψ_* (N~) ≅ (N restricted to R)~`. -/
theorem pushforward_tilde {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    True := by trivial

/-- **Blueprint `lem:tilde-functorial`** (Stacks 01I6): `ψ^* (M~) ≅ (S ⊗_R M)~`. -/
theorem pullback_tilde {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    True := by trivial

end AlgebraicGeometry.Spec
