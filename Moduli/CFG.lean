/-!
# General criterion for categories fibered in groupoids (CFG)

This file proves the general category-theoretic criterion characterising when a fibered category
`p : 𝒳 ⥤ 𝒮` is fibered in groupoids (i.e., all fibres are groupoids). The three main results are:

- `isStronglyCartesian_of_fiber_groupoid` (cfg-suff): if `p` is fibered and every fibre is a
  groupoid, then every morphism over any base arrow is strongly Cartesian.

- `groupoidFiberOfAllStronglyCartesian` (cfg-nec): if every morphism in `𝒳` lying over any base
  arrow is strongly Cartesian, then each fibre `p.Fiber S` is a groupoid.

- `isFiberedInGroupoids_iff` (cfg-criterion): the iff combining the two for a fibered `p`.

Namespace: `CategoryTheory.Functor` (generic placement, matching Mathlib conventions).
-/

import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Groupoid

open CategoryTheory Category IsHomLift IsStronglyCartesian Functor

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮)

/-! ### Auxiliary: the inverse of an identity-lift is an identity-lift -/

/-- If `φ : a ⟶ b` lifts `𝟙 S` through `p` and is an isomorphism in `𝒳`, then `inv φ` also
lifts `𝟙 S`. The proof computes `p.map (inv φ) = inv (p.map φ)` and uses `of_fac'`. -/
private lemma isHomLift_inv_of_id_lift {S : 𝒮} {a b : 𝒳} {φ : a ⟶ b}
    (hlift : p.IsHomLift (𝟙 S) φ) [IsIso φ] : p.IsHomLift (𝟙 S) (inv φ) := by
  haveI := hlift
  have ha : p.obj a = S := domain_eq p (𝟙 S) φ
  have hb : p.obj b = S := codomain_eq p (𝟙 S) φ
  apply IsHomLift.of_fac' p (𝟙 S) (inv φ) hb ha
  -- Goal: p.map (inv φ) = eqToHom hb ≫ 𝟙 S ≫ eqToHom ha.symm
  have hmap : p.map φ = eqToHom ha ≫ eqToHom hb.symm := by
    have := fac' p (𝟙 S) φ; simpa using this
  rw [Functor.map_inv, hmap]
  simp

/-! ## cfg-suff: fibre groupoids imply all morphisms are strongly Cartesian -/

/-- **(cfg-suff)** If `p : 𝒳 ⥤ 𝒮` is a fibered category whose fibre over every `S : 𝒮` is a
groupoid, then every morphism `φ : a ⟶ b` in `𝒳` lying over any `f : R ⟶ S` is strongly
Cartesian.

**Proof.** Choose a strongly Cartesian lift `λ : c ⟶ b` of `f` with codomain `b`. The universal
property of `λ` factors `φ = v ≫ λ` where `v : a ⟶ c` lies over `𝟙 R`. Viewed as a morphism in
the fibre `Fiber p R` (which is a groupoid), `v` is an iso in `𝒳`. An iso lying over a base arrow
is strongly Cartesian (`IsStronglyCartesian.of_isIso`); the composite of two strongly Cartesian
morphisms is strongly Cartesian. -/
theorem isStronglyCartesian_of_fiber_groupoid [p.IsFibered] [∀ S, Groupoid (p.Fiber S)]
    {a b : 𝒳} {R S : 𝒮} {f : R ⟶ S} {φ : a ⟶ b} [p.IsHomLift f φ] :
    p.IsStronglyCartesian f φ := by
  have ha : p.obj a = R := domain_eq p f φ
  have hb : p.obj b = S := codomain_eq p f φ
  -- Choose a Cartesian lift λ : c ⟶ b of f with codomain b
  obtain ⟨c, λ, hλ⟩ := IsPreFibered.exists_isCartesian (p := p) hb f
  -- In IsFibered every Cartesian morphism is strongly Cartesian
  haveI hsc_λ : p.IsStronglyCartesian f λ := IsFibered.isStronglyCartesian_of_isCartesian p f λ
  have hc : p.obj c = R := domain_eq p f λ
  -- Factor φ = v ≫ λ via the universal property of λ (over 𝟙 R ≫ f = f)
  set v := IsStronglyCartesian.map p f λ (f' := 𝟙 R ≫ f) rfl φ
  haveI hv_lift : p.IsHomLift (𝟙 R) v := inferInstance
  have hv_fac : v ≫ λ = φ := IsStronglyCartesian.fac p f λ rfl φ
  -- View v as a morphism in the fibre Fiber p R
  let av : p.Fiber R := ⟨a, ha⟩
  let cv : p.Fiber R := ⟨c, hc⟩
  let vFib : av ⟶ cv := ⟨v, hv_lift⟩
  -- Groupoid instance makes vFib an iso (IsIso.of_groupoid)
  haveI : IsIso vFib := inferInstance
  -- So v = fiberInclusion.map vFib is an iso in 𝒳
  haveI hv_iso : IsIso v := Functor.map_isIso Fiber.fiberInclusion vFib
  -- φ = v ≫ λ with v iso (hence strongly Cartesian over 𝟙 R) and λ strongly Cartesian over f,
  -- so v ≫ λ is strongly Cartesian over 𝟙 R ≫ f
  rw [← hv_fac]
  haveI : p.IsStronglyCartesian (𝟙 R) v := inferInstance
  haveI hcomp : p.IsStronglyCartesian (𝟙 R ≫ f) (v ≫ λ) := inferInstance
  simpa using hcomp

/-! ## cfg-nec: all morphisms strongly Cartesian implies fibre groupoids -/

/-- **(cfg-nec)** If every morphism `φ : a ⟶ b` with `p.IsHomLift f φ` is strongly Cartesian,
then each fibre `p.Fiber S` is a groupoid.

**Proof.** Any morphism `vFib : av ⟶ bv` in `Fiber p S` has `vFib.val` lying over `𝟙 S`. By
hypothesis `vFib.val` is strongly Cartesian over `𝟙 S`; since `𝟙 S` is an iso, `vFib.val` is an
iso in `𝒳` (`isIso_of_base_isIso`). Its inverse `inv vFib.val` also lies over `𝟙 S`
(`isHomLift_inv_of_id_lift`), giving the inverse morphism in the fibre. -/
noncomputable def groupoidFiberOfAllStronglyCartesian
    (h : ∀ {a b : 𝒳} {R S : 𝒮} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ],
        p.IsStronglyCartesian f φ)
    (S : 𝒮) : Groupoid (p.Fiber S) :=
  Groupoid.ofIsIso fun {av bv} vFib => by
    haveI hvFib_lift : p.IsHomLift (𝟙 S) vFib.val := vFib.2
    -- vFib.val is strongly Cartesian over 𝟙 S by hypothesis
    haveI hsc : p.IsStronglyCartesian (𝟙 S) vFib.val := h (𝟙 S) vFib.val
    -- Since 𝟙 S is an iso, vFib.val is an iso in 𝒳
    haveI hiso_val : IsIso vFib.val := IsStronglyCartesian.isIso_of_base_isIso vFib.val
    -- The inverse inv vFib.val also lifts 𝟙 S
    haveI hinv_lift : p.IsHomLift (𝟙 S) (inv vFib.val) :=
      isHomLift_inv_of_id_lift p hvFib_lift
    -- Build the iso in Fiber p S
    refine ⟨⟨⟨inv vFib.val, hinv_lift⟩, ?_, ?_⟩⟩
    · ext; simp
    · ext; simp

/-! ## cfg-criterion: the iff for fibered categories -/

/-- **(cfg-criterion)** For a fibered category `p : 𝒳 ⥤ 𝒮`, the following are equivalent:
1. Every fibre `p.Fiber S` is a groupoid.
2. Every morphism `φ : a ⟶ b` in `𝒳` lying over any `f : R ⟶ S` is strongly Cartesian. -/
theorem isFiberedInGroupoids_iff [p.IsFibered] :
    (∀ S, Groupoid (p.Fiber S)) ↔
    ∀ {a b : 𝒳} {R S : 𝒮} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ],
        p.IsStronglyCartesian f φ := by
  constructor
  · intro hG {a} {b} {R} {S} f φ hφ
    haveI : ∀ S, Groupoid (p.Fiber S) := hG
    exact isStronglyCartesian_of_fiber_groupoid p
  · intro hSC S
    exact groupoidFiberOfAllStronglyCartesian p hSC S

end CategoryTheory.Functor
