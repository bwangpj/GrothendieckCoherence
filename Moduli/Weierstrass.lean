import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Opposites

/-!
# The fibered category of Weierstrass curves (Blueprint §3, milestones M1–M2)

Following `moduli_ell_blueprint`, we build the category `𝒲` of Weierstrass curves
fibered over the category of affine schemes `Aff = CommRingCatᵒᵖ`, and show its
projection is fibered in groupoids (a CFG).

* An **object** is a pair `(R, W)` with `R : CommRingCat` and
  `W : WeierstrassCurve R`.
* A **morphism** `(R, W) ⟶ (R', W')` is a pair `(f, C)` where `f : R' ⟶ R` is a
  ring map (an `Aff`-arrow `Spec R → Spec R'`) and `C : VariableChange R` with
  `C • W = W'.map f` (Blueprint eq. (3)).

The M1 equivariance input `WeierstrassCurve.map_variableChange`
(`(C.map φ) • (W.map φ) = (C • W).map φ`) is already in Mathlib
(`Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`), as are
`WeierstrassCurve.map_id`, `map_map`, and `VariableChange.map_id`, `map_map`.
-/

open CategoryTheory WeierstrassCurve

universe u

namespace AlgebraicGeometry.EllipticCurve.Moduli

/-! ## M1: group-homomorphism lemmas for `VariableChange.map` (if absent upstream) -/

namespace WeierstrassCurve.VariableChange

variable {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)

/-- `VariableChange.map φ` preserves the identity. -/
@[simp] lemma map_one : (1 : WeierstrassCurve.VariableChange R).map φ = 1 :=
  (_root_.WeierstrassCurve.VariableChange.mapHom φ).map_one

/-- `VariableChange.map φ` preserves multiplication (it is a group homomorphism). -/
@[simp] lemma map_mul (C C' : WeierstrassCurve.VariableChange R) :
    (C * C').map φ = C.map φ * C'.map φ :=
  (_root_.WeierstrassCurve.VariableChange.mapHom φ).map_mul C C'

end WeierstrassCurve.VariableChange

/-! ## M2: the total category `𝒲` -/

/-- An object of `𝒲`: a commutative ring `R` together with a Weierstrass curve
over `R`. -/
structure Weierstrass where
  /-- The base ring `R` (an object of `Aff = CommRingCatᵒᵖ` read as `Spec R`). -/
  base : CommRingCat.{u}
  /-- The Weierstrass curve over `R`. -/
  curve : WeierstrassCurve base

namespace Weierstrass

/-- A morphism `(R, W) ⟶ (R', W')` in `𝒲`: an `Aff`-arrow `Spec R → Spec R'`,
i.e. a ring map `f : R' ⟶ R`, together with a variable change `C : VariableChange R`
satisfying `C • W = W'.map f`. -/
structure Hom (X Y : Weierstrass.{u}) where
  /-- The base ring map `f : Y.base ⟶ X.base` (the `Aff`-arrow `Spec X → Spec Y`). -/
  baseHom : Y.base ⟶ X.base
  /-- The variable-change component `C : VariableChange X.base`. -/
  vc : WeierstrassCurve.VariableChange X.base
  /-- Compatibility (Blueprint eq. (3)): `C • W = W'.map f`. -/
  cond : vc • X.curve = Y.curve.map baseHom.hom

attribute [simp] Hom.cond

/-- Extensionality for morphisms of `𝒲`. -/
@[ext] lemma Hom.ext {X Y : Weierstrass.{u}} {φ ψ : Hom X Y}
    (hbase : φ.baseHom = ψ.baseHom) (hvc : φ.vc = ψ.vc) : φ = ψ := by
  obtain ⟨f, C, hC⟩ := φ
  obtain ⟨g, D, hD⟩ := ψ
  dsimp only at hbase hvc
  subst hbase
  subst hvc
  rfl

/-- The identity morphism `(R, W) ⟶ (R, W)`: `(𝟙_R, 1)`. -/
@[simps] def Hom.id (X : Weierstrass.{u}) : Hom X X where
  baseHom := 𝟙 X.base
  vc := 1
  cond := by simp [WeierstrassCurve.map_id]

/-- Composition of morphisms in `𝒲`. If `φ = (f, C) : X ⟶ Y` and
`ψ = (g, C') : Y ⟶ Z`, the composite is `(g ≫ f, (C'.map f) * C)`. -/
@[simps] def Hom.comp {X Y Z : Weierstrass.{u}} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  baseHom := ψ.baseHom ≫ φ.baseHom
  vc := ψ.vc.map φ.baseHom.hom * φ.vc
  cond := by
    have h1 := φ.cond
    have h2 := ψ.cond
    rw [mul_smul, h1, WeierstrassCurve.map_variableChange, h2,
      WeierstrassCurve.map_map, CommRingCat.hom_comp]

instance : Category Weierstrass.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp φ := Hom.ext (by simp [Hom.comp, Hom.id]) (by
    simp [Hom.comp, Hom.id, CommRingCat.hom_id, WeierstrassCurve.VariableChange.map_id])
  comp_id φ := Hom.ext (by simp [Hom.comp, Hom.id]) (by
    simp [Hom.comp, Hom.id, WeierstrassCurve.VariableChange.map_one])
  assoc φ ψ χ := Hom.ext (by simp [Hom.comp]) (by
    simp [Hom.comp, CommRingCat.hom_comp, WeierstrassCurve.VariableChange.map_mul,
      WeierstrassCurve.VariableChange.map_map, mul_assoc])

/-! ## M2: the projection `p : 𝒲 → Aff` -/

/-- The projection functor `p_𝒲 : 𝒲 → Aff = CommRingCatᵒᵖ`, sending `(R, W) ↦ Spec R`
(i.e. `op R`) and `(f, C) ↦ f` (i.e. `f.op`). -/
@[simps] def proj : Weierstrass.{u} ⥤ CommRingCatᵒᵖ where
  obj X := Opposite.op X.base
  map φ := (φ.baseHom).op
  map_id _ := rfl
  map_comp _ _ := rfl

end Weierstrass

end AlgebraicGeometry.EllipticCurve.Moduli
