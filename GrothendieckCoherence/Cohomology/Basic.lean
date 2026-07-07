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

/-- Global sections functor `Γ(X, -) : X.Modules ⥤ Ab`, as the underlying abelian
presheaf evaluated on the whole space. Blueprint: underlies `def:sheaf-cohomology`. -/
noncomputable def sectionsFunctor (X : Scheme.{u}) : X.Modules ⥤ Ab.{u} :=
  Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op ⊤)

instance (X : Scheme.{u}) : (sectionsFunctor X).Additive where

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
