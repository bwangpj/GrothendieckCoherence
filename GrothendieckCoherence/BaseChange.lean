import Mathlib
import GrothendieckCoherence.Cohomology.Basic
import GrothendieckCoherence.Coherent.Basic

/-!
# Cohomology and base change (Mumford, *Abelian Varieties*, p. 53)

**Theorem 0.1** (Mumford, *Abelian Varieties*, p. 53; also EGA III.7.7–7.9,
Hartshorne III.12, Stacks [0A1H](https://stacks.math.columbia.edu/tag/0A1H)):

> If `f : X → Y` is a proper morphism, `Y` is affine, `ℱ` is coherent on `X` and
> flat over `Y`, and if for some `n` we have `Hⁿ(X_y, ℱ_y) = 0` for all `y ∈ Y`,
> then `Rⁿ⁻¹ f_* ℱ` commutes with all base changes.

## Key definitions

* `FlatOver f F` — stalkwise flatness of `F` over `Y` via `f`.
* `FiberCohomologyVanishes f F n` — `Hⁿ(f.fiber y, ℱ_y) = 0` for all `y`.
* `baseChangeMap f F i g` — the natural base-change comparison map
  `g^*(Rⁱ f_* F) ⟶ Rⁱ f'_* (g'^* F)` for a base change `g : Y' ⟶ Y`.
* `CommutesWithBaseChange f F i` — `baseChangeMap` is an iso for every `g`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-!
### Relative flatness
`ℱ` is **flat over `Y` along `f`** if for every point `x : X` the stalk
`F.presheaf.stalk x` is flat as a module over `𝒪_{Y, f(x)}`, where the
`𝒪_{Y, f(x)}`-action is restriction of scalars along the stalk map
`f.stalkMap x : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x`.

More precisely, `TopCat.Presheaf.stalk F.presheaf x` carries an
`X.presheaf.stalk x`-module structure (via `PresheafOfModules`), and hence
a `Y.presheaf.stalk (f x)`-module structure via `(f.stalkMap x).hom`;
flatness is `Module.Flat (Y.presheaf.stalk (f x)) _` for that restricted
scalar action.
-/

-- `set_option backward.isDefEq.respectTransparency false` is needed so that Lean unfolds
-- `X.ringCatSheaf.obj = X.presheaf ⋙ forget₂ CommRingCat RingCat` during instance synthesis
-- for the `PresheafOfModules.stalk` `Module`-instance from `Stalk.lean:192`.
-- The docstring is placed after `set_option … in` so that it attaches to `def FlatOver`.
set_option backward.isDefEq.respectTransparency false in
/-- `F` is **flat over the base** of `f : X ⟶ Y`: for every point `x : X`,
the stalk `F.val.presheaf.stalk x` is flat as a module over the local ring
`𝒪_{Y, f(x)}` acting via restriction of scalars along `f.stalkMap x`.

Mathlib API used:
- `f.stalkMap x : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x`
  (`AlgebraicGeometry.Scheme.Hom.stalkMap`)
- `TopCat.Presheaf.stalk F.val.presheaf x` is a module over `X.presheaf.stalk x`
  via `PresheafOfModules` (instance from `Mathlib.Algebra.Category.ModuleCat.Stalk:192`).
- `Module.Flat R M` (`Mathlib.RingTheory.Flat.Basic`). -/
def FlatOver (F : X.Modules) (f : X ⟶ Y) : Prop :=
  ∀ x : X,
    -- `PresheafOfModules.stalk` (Stalk.lean:192) gives
    -- `Module (X.presheaf.stalk x) ↑(F.val.presheaf.stalk x)`.
    -- `Module.compHom` restricts scalars along `(f.stalkMap x).hom`.
    letI : Module (Y.presheaf.stalk (f x)) ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
      Module.compHom (M := ↑(TopCat.Presheaf.stalk F.val.presheaf x)) (f.stalkMap x).hom
    Module.Flat (Y.presheaf.stalk (f x)) ↑(TopCat.Presheaf.stalk F.val.presheaf x)

/-!
### Fibrewise cohomology vanishing

The **scheme-theoretic fibre** of `f : X ⟶ Y` at `y : Y` is
`f.fiber y := pullback f (Y.fromSpecResidueField y)`
(`AlgebraicGeometry.Scheme.Hom.fiber`, from `Mathlib.AlgebraicGeometry.Fiber`).
The embedding is `f.fiberι y : f.fiber y ⟶ X`.

The **restriction** of `F` to the fibre is
`(Modules.pullback (f.fiberι y)).obj F : (f.fiber y).Modules`.

Sheaf cohomology `Hⁿ(f.fiber y, ℱ_y)` is
`(Scheme.cohomology (f.fiber y) n).obj ((Modules.pullback (f.fiberι y)).obj F)`.

Vanishing says this object is zero in `Ab` (i.e., `IsZero`).
-/

/-- **Fibrewise cohomology vanishing** in degree `n`:
`Hⁿ(X_y, ℱ_y) = 0` for every point `y ∈ Y`, where:
- `X_y = f.fiber y = pullback f (Y.fromSpecResidueField y)` is the
  scheme-theoretic fibre (`AlgebraicGeometry.Scheme.Hom.fiber`),
- `ℱ_y = (Modules.pullback (f.fiberι y)).obj F` is the pullback of `F`
  along the fibre embedding `f.fiberι y : X_y ⟶ X`, and
- `Hⁿ(X_y, ℱ_y)` is `(Scheme.cohomology (f.fiber y) n).obj ℱ_y`. -/
def FiberCohomologyVanishes (F : X.Modules) (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ y : Y,
    IsZero ((Scheme.cohomology (f.fiber y) n).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι y)).obj F))

/-!
### Base-change map and commutativity

For a cartesian square
```
X' = X ×_Y Y' --p--> X
      |                |
      f'               f
      ↓                ↓
      Y' -----g------> Y
```
where `p = pullback.fst f g : X' ⟶ X` and `f' = pullback.snd f g : X' ⟶ Y'`,
the **base-change map** is the natural morphism
`g^*(Rⁱ f_* F) ⟶ Rⁱ f'_* (p^* F)`
comparing cohomology with base change.
-/

/-- The **base-change comparison map** for the cartesian square
`X' = pullback f g`, `p = pullback.fst f g`, `f' = pullback.snd f g`:
```
  g^*(Rⁱ f_* F)  ⟶  Rⁱ f'_* (p^* F)
```
The source is `(Scheme.Modules.pullback g).obj ((Scheme.higherDirectImage f i).obj F)` and
the target is `(Scheme.higherDirectImage (pullback.snd f g) i).obj
  ((Scheme.Modules.pullback (pullback.fst f g)).obj F)`.

Construction is deferred to `sorry`; the type is genuine. A rigorous proof
requires the Grothendieck spectral sequence or EGA III base-change machinery,
which is not yet in Mathlib. -/
noncomputable def baseChangeMap (f : X ⟶ Y) (F : X.Modules) (i : ℕ)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).obj ((Scheme.higherDirectImage f i).obj F) ⟶
      (Scheme.higherDirectImage (pullback.snd f g) i).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst f g)).obj F) := sorry

/-- `Rⁱ f_* ℱ` **commutes with all base changes**: for every morphism
`g : Y' ⟶ Y`, the base-change map
`g^*(Rⁱ f_* F) ⟶ Rⁱ f'_* (p^* F)` (where `p = pullback.fst f g`,
`f' = pullback.snd f g`) is an isomorphism.

This is the predicate appearing in Mumford's Theorem 0.1. -/
def CommutesWithBaseChange (F : X.Modules) (f : X ⟶ Y) (i : ℕ) : Prop :=
  ∀ ⦃Y' : Scheme.{u}⦄ (g : Y' ⟶ Y), IsIso (baseChangeMap f F i g)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- **Theorem 0.1 (Mumford, *Abelian Varieties*, p. 53; cohomology and base
change).** Let `f : X ⟶ Y` be proper with `Y` affine, and let `ℱ` be coherent on
`X` and flat over `Y`. If `Hⁿ(X_y, ℱ_y) = 0` for all `y ∈ Y` (for some fixed `n`),
then `Rⁿ⁻¹ f_* ℱ` commutes with all base changes.

The proof is deferred to `sorry`; the full argument requires EGA III.7.7–7.9
or Mumford's spectral-sequence argument (not yet formalised in Mathlib). -/
theorem higherDirectImage_commutesWithBaseChange_of_fiberVanishing
    (f : X ⟶ Y) [IsProper f] [IsAffine Y]
    (F : X.Modules) (hcoh : F.IsCoherent) (hflat : F.FlatOver f)
    (n : ℕ) (hvanish : F.FiberCohomologyVanishes f n) :
    F.CommutesWithBaseChange f (n - 1) := sorry

end AlgebraicGeometry.Scheme
