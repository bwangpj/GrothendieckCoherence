import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# M0 substrate audit (revised blueprint §7)

This file proves (as `example`s) that every Mathlib substrate declaration required by
the blueprint exists with the expected orientation and typeclass context.
Nothing is exported; every item has a one-line comment citing the blueprint label.
-/

open WeierstrassCurve CategoryTheory

namespace AlgebraicGeometry.EllipticCurve.Moduli.SubstrateAudit

/-! ## §7.1  VariableChange.mapHom and map_one / map_mul -/

section VCMap

variable {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
variable (C C' : WeierstrassCurve.VariableChange R)

-- blueprint lem:vc-mapHom: mapHom φ is a group hom VariableChange R →* VariableChange A
example : WeierstrassCurve.VariableChange.mapHom φ C = C.map φ := rfl

-- blueprint lem:vc-map-one: (1 : VariableChange R).map φ = 1
example : (1 : WeierstrassCurve.VariableChange R).map φ = 1 :=
  (WeierstrassCurve.VariableChange.mapHom φ).map_one

-- blueprint lem:vc-map-mul
example : (C * C').map φ = C.map φ * C'.map φ :=
  (WeierstrassCurve.VariableChange.mapHom φ).map_mul C C'

end VCMap

/-! ## §7.2  VariableChange.map_id and map_map -/

section VCMapId

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] {B : Type*} [CommRing B]
variable (C : WeierstrassCurve.VariableChange R)
variable (φ : R →+* A) (ψ : A →+* B)

-- blueprint lem:vc-map-id
example : C.map (RingHom.id R) = C :=
  WeierstrassCurve.VariableChange.map_id C

-- blueprint lem:vc-map-map
example : (C.map φ).map ψ = C.map (ψ.comp φ) :=
  WeierstrassCurve.VariableChange.map_map C φ ψ

end VCMapId

/-! ## §7.3  WeierstrassCurve.map_variableChange (orientation check) -/

section MapVC

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A]
variable (C : WeierstrassCurve.VariableChange R) (W : WeierstrassCurve R) (φ : R →+* A)

-- blueprint eq:map-variableChange: (C.map f) • (W.map f) = (C • W).map f
example : (C.map φ) • (W.map φ) = (C • W).map φ :=
  WeierstrassCurve.map_variableChange W C φ

end MapVC

/-! ## §7.4  WeierstrassCurve.map_id, map_map, map_Δ -/

section WCMap

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] {B : Type*} [CommRing B]
variable (W : WeierstrassCurve R) (f : R →+* A) (g : A →+* B)

-- blueprint lem:map-id
example : W.map (RingHom.id R) = W :=
  WeierstrassCurve.map_id W

-- blueprint lem:map-map
example : (W.map f).map g = W.map (g.comp f) :=
  WeierstrassCurve.map_map W f g

-- blueprint lem:map-Delta (spelled map_Δ in Mathlib)
example : (W.map f).Δ = f W.Δ :=
  WeierstrassCurve.map_Δ W f

end WCMap

/-! ## §7.5  variableChange_j (requires W.IsElliptic) -/

section VCJ

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
variable (C : WeierstrassCurve.VariableChange R)

-- blueprint warn:j-typeclass — [W.IsElliptic] is required; j is only defined for elliptic W
-- blueprint lem:variableChange-j: (C • W).j = W.j
example : (C • W).j = W.j :=
  WeierstrassCurve.variableChange_j W C

end VCJ

/-! ## §7.6  map_j -/

section MapJ

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A]
variable (W : WeierstrassCurve R) [W.IsElliptic] (f : R →+* A)

-- blueprint lem:map-j: (W.map f).j = f W.j
example : (W.map f).j = f W.j :=
  WeierstrassCurve.map_j W f

end MapJ

/-! ## §7.7  ofJ_j over a field -/

section OfJJ

variable {F : Type*} [Field F] [DecidableEq F] (j : F)

-- blueprint lem:ofJ-j: (ofJ j).j = j (over a field)
example : (WeierstrassCurve.ofJ j).j = j :=
  WeierstrassCurve.ofJ_j j

end OfJJ

/-! ## §7.8  Ellipticity instances -/

section EllipticityInstances

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
variable {A : Type*} [CommRing A] (f : R →+* A)
variable (C : WeierstrassCurve.VariableChange R)

-- blueprint lem:elliptic-map: (W.map f).IsElliptic
example : (W.map f).IsElliptic := inferInstance

-- blueprint lem:elliptic-variableChange: (C • W).IsElliptic
example : (C • W).IsElliptic := inferInstance

end EllipticityInstances

/-! ## §7.9  FiberedCategory API #checks -/

section FiberedAPI

-- blueprint ref:isFibered-of-exists-isStronglyCartesian
#check @CategoryTheory.Functor.IsFibered.of_exists_isStronglyCartesian

-- blueprint ref:isStronglyCartesian-comp
#check @CategoryTheory.Functor.IsStronglyCartesian.comp

-- blueprint ref:isStronglyCartesian-isIso-of-base-isIso
#check @CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso

-- blueprint ref:Fiber
#check @CategoryTheory.Functor.Fiber

-- blueprint ref:fiberInclusion
#check @CategoryTheory.Functor.Fiber.fiberInclusion

-- blueprint ref:Pseudofunctor-CoGrothendieck
#check @CategoryTheory.Pseudofunctor.CoGrothendieck

end FiberedAPI

end AlgebraicGeometry.EllipticCurve.Moduli.SubstrateAudit
