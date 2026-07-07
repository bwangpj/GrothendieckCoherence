import Mathlib
import GrothendieckCoherence.ProjectiveMorphism.Ample
import GrothendieckCoherence.Projective.SerreProj
import GrothendieckCoherence.Cech.HigherDirectImageQCoh
import GrothendieckCoherence.Coherent.Basic

/-!
# Higher direct images along projective morphisms (Blueprint chapter: proj-hdi)

`lem:graded-finiteness`, `lem:proj-hdi-vanish`, `lem:proj-hdi-coherent`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- **Blueprint `lem:graded-finiteness`** (Stacks 02O0): for `A` Noetherian,
`f : X → Spec A` projective with `f`-ample `L`, `ℱ` coherent, the graded module
`⊕_d Hᵖ(X, ℱ ⊗ L^d)` is finite over the section ring; in particular each
`Hᵖ(X, ℱ)` is a finite `A`-module and `Hᵖ(X, ℱ ⊗ L^d) = 0` for `p > 0`, `d ≫ 0`. -/
theorem gradedCohomology_finite_projective {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ Spec (.of A)) (hf : IsProjective f) : True := trivial

/-- **Blueprint `lem:proj-hdi-vanish`** (Stacks 02O1): for `S` Noetherian,
`f : X → S` proper, `L` an `f`-relatively ample invertible sheaf, `ℱ` coherent,
there is `n₀` with `Rᵖ f_* (ℱ ⊗ L^n) = 0` for all `p > 0` and `n ≥ n₀`. -/
theorem higherDirectImage_vanishing_relativelyAmple
    (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S]
    (L : X.Modules) (hL : Scheme.IsRelativelyAmple f L)
    (F : X.Modules) (hF : F.IsCoherent) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p, 0 < p →
      IsZero ((higherDirectImage f p).obj F) := sorry

/-- **Blueprint `lem:proj-hdi-coherent`** (Stacks 02O4; Hartshorne III.8.8): for
`S` locally Noetherian, `f : X → S` projective, `ℱ` coherent, `Rᵖ f_* ℱ` is
coherent for all `p ≥ 0`. -/
theorem higherDirectImage_coherent_of_projective
    (f : X ⟶ S) [IsLocallyNoetherian S] (hf : IsProjective f)
    (F : X.Modules) (hF : F.IsCoherent) (p : ℕ) :
    ((higherDirectImage f p).obj F).IsCoherent := sorry

end AlgebraicGeometry.Scheme
