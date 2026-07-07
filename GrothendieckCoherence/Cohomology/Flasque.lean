import Mathlib
import GrothendieckCoherence.Cohomology.Basic

/-!
# Flasque sheaves and acyclic resolutions (Blueprint chapter: flasque)

The light replacement for the relative Leray spectral sequence:
`def:flasque`, `lem:injective-flasque`, `lem:pushforward-flasque`,
`lem:flasque-acyclic`, `lem:acyclic-resolution`, `lem:acyclic-pushforward`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe v u

namespace TopCat.Presheaf

-- `IsFlasque` is now a class in Mathlib (`TopCat.Presheaf.IsFlasque`):
--   class IsFlasque (F : Presheaf C X) : Prop where
--     epi : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (F.map i)
-- **Blueprint `def:flasque`** (Stacks 01AF): a presheaf is *flasque* if every
-- restriction map `F(U) → F(V)` for `V ⊆ U` is an epimorphism (surjective).

-- `isFlasque_pushforward` / **Blueprint `lem:pushforward-flasque`** (Stacks 01E9):
-- if `F` is flasque and `g` continuous then `g_* F` is flasque.
-- This is now `TopCat.Presheaf.IsFlasque.pushforward_isFlasque` in Mathlib.

end TopCat.Presheaf

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- **Blueprint `lem:injective-flasque`** (Stacks 01EA): every injective
`𝒪_X`-module is flasque. -/
theorem Modules.injective_isFlasque (M : X.Modules) [Injective M] :
    M.presheaf.IsFlasque := sorry

/-- **Blueprint `lem:flasque-acyclic`** (Stacks 01EB): a flasque sheaf `ℱ` has
`Hⁱ(X, ℱ) = 0` and `Rⁱ f_* ℱ = 0` for all `i > 0`. Recorded for `Rⁱ f_*`. -/
theorem higherDirectImage_flasque_eq_zero (f : X ⟶ Y) (M : X.Modules)
    (hM : M.presheaf.IsFlasque) (i : ℕ) (hi : 0 < i) :
    IsZero ((higherDirectImage f i).obj M) := sorry

/-- **Blueprint `lem:acyclic-resolution`** (Stacks 0156): derived functors are
computed by acyclic resolutions. Recorded as a placeholder statement. -/
theorem cohomology_of_acyclicResolution (X : Scheme.{u}) (M : X.Modules) (i : ℕ) :
    True := trivial

/-- **Blueprint `lem:acyclic-pushforward`** (the Note): for
`X --g--> X' --f--> Y` with `R^q g_* B = 0` for all `q > 0`, there is a natural
isomorphism `R^q f_* (g_* B) ≅ R^q (f ∘ g)_* B` for all `q ≥ 0`.

This is the key lemma that replaces the relative Leray spectral sequence in the
finiteness proof. -/
noncomputable def higherDirectImage_pushforward_of_acyclic
    (g : X ⟶ Y) (f : Y ⟶ Z) (B : X.Modules)
    (hB : ∀ q, 0 < q → IsZero ((higherDirectImage g q).obj B)) (q : ℕ) :
    (higherDirectImage f q).obj ((Modules.pushforward g).obj B) ≅
      (higherDirectImage (g ≫ f) q).obj B := sorry

end AlgebraicGeometry.Scheme
