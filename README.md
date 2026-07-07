# GrothendieckCoherence

A Lean 4 / Mathlib formalisation project targeting **Grothendieck's Coherence
Theorem** (EGA III, Théorème 3.2.1; Stacks [02O5](https://stacks.math.columbia.edu/tag/02O5)):

> Let `Y` be a locally Noetherian scheme and `f : X ⟶ Y` a proper morphism.
> For every coherent `𝒪_X`-module `ℱ` and every `n ≥ 0`, the `𝒪_Y`-module
> `Rⁿ f_* ℱ` is coherent.

In the form driving the Lean statement:

```lean
theorem AlgebraicGeometry.Scheme.rightDerivedPushforward_isFinitePresentation_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsFinitePresentation] (n : ℕ) :
    (((Modules.pushforward f).rightDerived n).obj M).IsFinitePresentation
```

## Status

This is a **blueprint-driven scaffold**. Every mathematical statement from the
blueprint appears as a Lean declaration, currently discharged by `sorry` (and
placeholder `def`s for notions not yet in Mathlib). The project `lake build`s
cleanly modulo `sorry` warnings. Filling the `sorry`s is the formalisation work.

The blueprint itself lives at [`blueprint/src/content.tex`](blueprint/src/content.tex)
(PDF in [`docs/`](docs/)). See [`docs/BLUEPRINT_MAP.md`](docs/BLUEPRINT_MAP.md) for
the declaration ↔ blueprint-label ↔ Stacks-tag correspondence.

## Layout

The module tree mirrors the blueprint's work packages (WP1–WP9):

| Path | Blueprint part | Work package |
|------|----------------|--------------|
| `GrothendieckCoherence/QuasiCoherent/Tilde.lean` | Affine model `~(-)` | WP1 |
| `GrothendieckCoherence/QuasiCoherent/Basic.lean` | Quasi-coherent sheaves | WP1 |
| `GrothendieckCoherence/QuasiCoherent/Invertible.lean` | Invertible sheaves & twists | WP1 |
| `GrothendieckCoherence/Cohomology/Basic.lean` | `Hⁱ`, `Rⁱf_*`, δ-functor | WP2 |
| `GrothendieckCoherence/Cohomology/Flasque.lean` | Flasque / acyclic package | WP2 |
| `GrothendieckCoherence/Cohomology/Bridge.lean` | `rightDerived` ↔ `Rⁿf_*` | WP2 |
| `GrothendieckCoherence/Cech/Complex.lean` | Čech complex | WP3 |
| `GrothendieckCoherence/Cech/AffineVanishing.lean` | Serre vanishing on affines | WP3 |
| `GrothendieckCoherence/Cech/HigherDirectImageQCoh.lean` | qcoh of `Rⁱf_*` | WP3 |
| `GrothendieckCoherence/Projective/Twist.lean` | Twisting sheaves on Proj | WP4 |
| `GrothendieckCoherence/Projective/CohomologyProjectiveSpace.lean` | `Hⁱ(ℙⁿ, 𝒪(d))` | WP4 |
| `GrothendieckCoherence/Projective/SerreProj.lean` | Serre finiteness on Proj | WP4 |
| `GrothendieckCoherence/Coherent/Basic.lean` | Coherent sheaves | WP5 |
| `GrothendieckCoherence/Coherent/ClosedSupport.lean` | Closed immersions & support | WP5 |
| `GrothendieckCoherence/ProjectiveMorphism/Ample.lean` | Relative ampleness | WP6 |
| `GrothendieckCoherence/ProjectiveMorphism/HigherDirectImage.lean` | `Rᵖf_*` (projective) | WP6 |
| `GrothendieckCoherence/Devissage.lean` | Dévissage | WP7 |
| `GrothendieckCoherence/Chow.lean` | Chow's lemma | WP8 |
| `GrothendieckCoherence/Finiteness.lean` | The finiteness theorem | WP9 |
| `GrothendieckCoherence/Target.lean` | Bridge to the Lean statement | WP9 |

## Building

```sh
lake exe cache get   # fetch precompiled Mathlib oleans (first time)
lake build           # builds the whole project (sorry warnings expected)
```

Toolchain: `leanprover/lean4:v4.31.0`, Mathlib `v4.31.0` (pinned in `lakefile.toml`).

## References

EGA III 3.2.1; the Stacks Project (Ch. 20, 26, 27, 30); Hartshorne, *Algebraic
Geometry* III; Vakil, *The Rising Sea* §18.9. Per-declaration references are in
the docstrings and in `blueprint/src/content.tex`.
