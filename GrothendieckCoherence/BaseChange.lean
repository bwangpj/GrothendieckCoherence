import Mathlib
import GrothendieckCoherence.Cohomology.Basic
import GrothendieckCoherence.Coherent.Basic

/-!
# Cohomology and base change (Mumford, *Abelian Varieties*, p. 53)

**Theorem 0.1** of K. Buzzard, *Explicit models for modular curves*:

> If `f : X → Y` is a proper morphism, `Y` is affine, `ℱ` is coherent on `X` and
> flat over `Y`, and if for some `n` we have `Hⁿ(X_y, ℱ_y) = 0` for all `y ∈ Y`,
> then `Rⁿ⁻¹ f_* ℱ` commutes with all base changes.

This is a companion result to the coherence theorem (`Finiteness.lean`), built on
the same cohomological substrate (`higherDirectImage`) plus two new notions:
relative flatness of a sheaf over the base, and fibrewise cohomology. Both are
recorded here as placeholder predicates, together with the notion of a higher
direct image *commuting with base change*.

References: D. Mumford, *Abelian Varieties*, §II.5, p. 53 (Cohomology and Base
Change); EGA III.7.7–7.9; Hartshorne III.12; Stacks
[0A1H](https://stacks.math.columbia.edu/tag/0A1H).
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- `ℱ` is **flat over the base** of `f : X ⟶ Y`: each stalk of `ℱ` is a flat
module over the corresponding local ring of `Y` (via `f`). Placeholder predicate. -/
def FlatOver (f : X ⟶ Y) (F : X.Modules) : Prop := True

/-- **Fibrewise cohomology vanishing** in degree `n`: `Hⁿ(X_y, ℱ_y) = 0` for every
point `y ∈ Y`, where `X_y` is the fibre of `f` over `y` and `ℱ_y` the restriction
of `ℱ`. Placeholder predicate pending the fibre-cohomology API. -/
def FiberCohomologyVanishes (f : X ⟶ Y) (F : X.Modules) (n : ℕ) : Prop := True

/-- `Rⁱ f_* ℱ` **commutes with all base changes**: for every base-change morphism
`g : Y' ⟶ Y` with pullback square `X' = X ×_Y Y' → X`, the natural base-change map
`g^* (Rⁱ f_* ℱ) ⟶ Rⁱ f'_* (g'^* ℱ)` is an isomorphism. Placeholder predicate
pending the base-change-map construction. -/
def CommutesWithBaseChange (f : X ⟶ Y) (F : X.Modules) (i : ℕ) : Prop := True

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- **Theorem 0.1 (Mumford, *Abelian Varieties*, p. 53; cohomology and base
change).** Let `f : X ⟶ Y` be proper with `Y` affine, and let `ℱ` be coherent on
`X` and flat over `Y`. If `Hⁿ(X_y, ℱ_y) = 0` for all `y ∈ Y` (for some fixed `n`),
then `Rⁿ⁻¹ f_* ℱ` commutes with all base changes. -/
theorem higherDirectImage_commutesWithBaseChange_of_fiberVanishing
    (f : X ⟶ Y) [IsProper f] [IsAffine Y]
    (F : X.Modules) (hcoh : F.IsCoherent) (hflat : F.FlatOver f)
    (n : ℕ) (hvanish : F.FiberCohomologyVanishes f n) :
    F.CommutesWithBaseChange f (n - 1) := sorry

end AlgebraicGeometry.Scheme
