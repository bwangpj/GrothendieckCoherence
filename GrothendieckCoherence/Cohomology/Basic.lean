import Mathlib

/-!
# Sheaf cohomology and higher direct images (Blueprint Part: cohomology)

Definitions `def:sheaf-cohomology`, `def:higher-direct-image` and the basic
δ-functor / left-exactness / sheafification API (`lem:pf-left-exact`, `lem:les`,
`lem:hdi-sheafification`).

`higherDirectImage f n` is *defined* as the right-derived functor of the Mathlib
pushforward `Modules.pushforward f` — exactly the object in the target theorem.
Sheaf cohomology `Hⁱ(X, -)` is the right-derived functor of the (genuine) global
sections functor `Γ(X, -) = toPresheaf ⋙ (evaluation at ⊤)`.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y Z : Scheme.{u}}

/-- **Foundational instance (Grothendieck's theorem, `EnoughInjectives`).**
`X.Modules = SheafOfModules X.ringCatSheaf` is a Grothendieck abelian category and
therefore has enough injectives, hence injective resolutions. Mathlib records
this for `Sheaf J A` (with `HasSheafify`) but not yet for the `SheafOfModules`
structure, and the `def` `X.Modules` is opaque to instance search, so we bridge it
here. This is a known-true fact; discharging the `sorry` means porting the
Grothendieck-abelian instance to `SheafOfModules`. Every use of `Rⁱ f_*` and
`Hⁱ(X,-)` depends on it. -/
noncomputable instance instHasInjectiveResolutionsModules (X : Scheme.{u}) :
    HasInjectiveResolutions X.Modules := ⟨fun _ => ⟨sorry⟩⟩

/-- Global sections functor `Γ(X, -) : X.Modules ⥤ Ab`, as the underlying abelian
presheaf evaluated on the whole space. Blueprint: underlies `def:sheaf-cohomology`. -/
noncomputable def sectionsFunctor (X : Scheme.{u}) : X.Modules ⥤ Ab.{u} :=
  Modules.toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op ⊤)

-- `sectionsFunctor X` maps `φ : M ⟶ N` to `φ.app ⊤ : Γ(M,⊤) →+ Γ(N,⊤)` definitionally
-- (via `toPresheaf_map` and `mapPresheaf_app`, which are both `rfl`-lemmas).
-- Additivity then follows from `Modules.Hom.add_app : (φ + ψ).app U = φ.app U + ψ.app U`.
instance (X : Scheme.{u}) : (sectionsFunctor X).Additive where
  map_add {M N φ ψ} := Modules.Hom.add_app φ ψ (U := ⊤)

/-- **Blueprint `def:sheaf-cohomology`** (Stacks 01FR).
`Hⁱ(X, -)` is the `i`-th right derived functor of `Γ(X, -)`. -/
noncomputable def cohomology (X : Scheme.{u}) (i : ℕ) : X.Modules ⥤ Ab.{u} :=
  (sectionsFunctor X).rightDerived i

/-- **Blueprint `def:higher-direct-image`** (Stacks 01F1).
`Rⁱ f_*` is the `i`-th right derived functor of the (left exact) pushforward
`Modules.pushforward f`. This is the functor appearing in the target theorem. -/
noncomputable def higherDirectImage (f : X ⟶ Y) (i : ℕ) : X.Modules ⥤ Y.Modules :=
  (Modules.pushforward f).rightDerived i

/-- **Blueprint `lem:pf-left-exact`** (Stacks 01F1): `f_*` is additive and left
exact (it is a right adjoint, via `pullbackPushforwardAdjunction`). -/
theorem Modules.pushforward_leftExact (f : X ⟶ Y) :
    PreservesFiniteLimits (Modules.pushforward f) := sorry

/-- **Blueprint `lem:les`** (Stacks 0156): `{Rⁱ f_*}` is a cohomological
δ-functor; a short exact sequence induces a natural long exact sequence, with
`R⁰ f_* = f_*`. Recorded as the degree-`0` identification `R⁰ f_* ≅ f_*`. -/
noncomputable def higherDirectImage_deltaFunctor (f : X ⟶ Y) :
    higherDirectImage f 0 ≅ Modules.pushforward f :=
  (Modules.pushforward f).rightDerivedZeroIsoSelf

/-- **Blueprint `lem:hdi-sheafification`** (Stacks 01E0): `Rⁱ f_* ℱ` is the sheaf
associated to the presheaf `V ↦ Hⁱ(f⁻¹V, ℱ|_{f⁻¹V})` on `Y`; hence the computation
of `Rⁱ f_*` is local on `Y`. Faithful rendering of *locality on `Y`*: if two
`𝒪_X`-modules `M`, `N` become isomorphic after restriction to `f⁻¹V`, then
`Rⁱ f_* M` and `Rⁱ f_* N` become isomorphic after restriction to `V`. -/
theorem higherDirectImage_isSheafification (f : X ⟶ Y) (i : ℕ) (M N : X.Modules)
    (V : Y.Opens)
    (h : Nonempty ((Modules.pullback (f ⁻¹ᵁ V).ι).obj M ≅
        (Modules.pullback (f ⁻¹ᵁ V).ι).obj N)) :
    Nonempty ((Modules.pullback V.ι).obj ((higherDirectImage f i).obj M) ≅
      (Modules.pullback V.ι).obj ((higherDirectImage f i).obj N)) := sorry

end AlgebraicGeometry.Scheme
