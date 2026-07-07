import Mathlib
import GrothendieckCoherence.Devissage
import GrothendieckCoherence.Chow
import GrothendieckCoherence.ProjectiveMorphism.HigherDirectImage
import GrothendieckCoherence.Cohomology.Flasque
import GrothendieckCoherence.Coherent.ClosedSupport
import GrothendieckCoherence.Cech.HigherDirectImageQCoh

/-!
# The finiteness theorem (Blueprint chapter: finiteness)

`thm:finiteness`: coherence of higher direct images along a proper morphism.
This is the heart of the assembly — via dévissage (`coherent_devissage`), Chow's
lemma (`chowLemma`), the projective case (`higherDirectImage_coherent_of_projective`,
`higherDirectImage_vanishing_relativelyAmple`), the acyclic-pushforward lemma
(`higherDirectImage_pushforward_of_acyclic`), and closed immersions
(`closedImmersion_pushforward_coherent_and_acyclic`).
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- **Blueprint `thm:finiteness`** (Stacks 02O5; EGA III 3.2.1): let `S` be locally
Noetherian, `f : X → S` proper, `ℱ` coherent. Then `Rᵖ f_* ℱ` is coherent for all
`p ≥ 0`. -/
theorem higherDirectImage_coherent_of_isProper
    (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S]
    (F : X.Modules) (hF : F.IsCoherent) (p : ℕ) :
    ((higherDirectImage f p).obj F).IsCoherent := sorry

end AlgebraicGeometry.Scheme
