import GrothendieckCoherence.Moduli.Fibered
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Groupoid

set_option linter.style.whitespace false

/-!
# The moduli CFG `ℳ^W_{1,1}` and the j-invariant (Blueprint §4, milestone M3)

We construct the full subcategory `MW` of `Weierstrass` on elliptic curves
(objects `X : Weierstrass` with `X.curve.IsElliptic`) and prove it is a category
fibered in groupoids (CFG) over `Aff = CommRingCatᵒᵖ` via `MWProj = ellipticProp.ι ⋙ proj`.

## Main results

1. **Ellipticity stability** (Blueprint Lemmas 4.1–4.2):
   - `isElliptic_map`: `(W.map f).IsElliptic` — Mathlib, Weierstrass.lean:448.
   - `isElliptic_variableChange`: `(C • W).IsElliptic` — Mathlib, VariableChange.lean:225.

2. **The moduli category `MW`**: `ellipticProp.FullSubcategory` where
   `ellipticProp : ObjectProperty Weierstrass` sends `X` to `X.curve.IsElliptic`.
   `MWProj : MW ⥤ CommRingCatᵒᵖ` is `ellipticProp.ι ⋙ proj`.

3. **`MW` is a CFG**: `MWProj` is prefibered and fibered, with groupoid fibres.

4. **j-invariant** (Blueprint 4.9–4.11):
   - `variableChange_j_MW`: `(C • W).j = W.j`
   - `map_j_MW`: `(W.map f).j = f W.j`
   These give well-definedness of the j-invariant map.

## Mathlib names used
- Full subcategory: `CategoryTheory.ObjectProperty.FullSubcategory`
- `(W.map f).IsElliptic`: unnamed instance, Weierstrass.lean:448
- `(C • W).IsElliptic`: unnamed instance, VariableChange.lean:225
- `WeierstrassCurve.variableChange_Δ`: VariableChange.lean:218
- `WeierstrassCurve.variableChange_j`: VariableChange.lean:246 (section-level, not in namespace)
- `WeierstrassCurve.map_j`: Weierstrass.lean:470
-/

open CategoryTheory WeierstrassCurve Opposite

universe u

namespace AlgebraicGeometry.EllipticCurve.Moduli

open Weierstrass

/-! ## 1. Ellipticity stability -/

section EllipticityStability

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- Blueprint Lemma 4.1: ellipticity is stable under base change.
Delegates to the Mathlib instance at `Weierstrass.lean:448`, which uses
`WeierstrassCurve.map_Δ` and `IsUnit.map`. -/
lemma isElliptic_map {A : Type u} [CommRing A] (f : RingHom R A) : (W.map f).IsElliptic :=
  inferInstance

/-- Blueprint Lemma 4.2: ellipticity is stable under variable change.
The key identity `variableChange_Δ : (C • W).Δ = C.u⁻¹^12 * W.Δ` (VariableChange.lean:218)
shows `(C • W).Δ` is a unit, since `C.u⁻¹` is a unit and `W.Δ` is a unit by hypothesis.
Delegates to the Mathlib instance at `VariableChange.lean:225`. -/
lemma isElliptic_variableChange (C : WeierstrassCurve.VariableChange R) :
    (C • W).IsElliptic :=
  inferInstance

end EllipticityStability

/-! ## 2. The moduli category `MW` -/

/-- The ellipticity property on `Weierstrass` objects. -/
def ellipticProp : ObjectProperty Weierstrass.{u} :=
  fun X => X.curve.IsElliptic

/-- The moduli category `MW = ℳ^W_{1,1}`: full subcategory of `𝒲` on elliptic curves.
Objects are `⟨X : Weierstrass, hX : X.curve.IsElliptic⟩`; morphisms are `𝒲`-morphisms. -/
abbrev MW := ellipticProp.FullSubcategory (C := Weierstrass.{u})

/-- The projection functor `MWProj : MW ⥤ CommRingCatᵒᵖ`. -/
def MWProj : MW.{u} ⥤ CommRingCatᵒᵖ :=
  ellipticProp.ι ⋙ proj

@[simp] lemma MWProj_obj (X : MW.{u}) : MWProj.obj X = Opposite.op X.obj.base := rfl

@[simp] lemma MWProj_map {X Y : MW.{u}} (f : X ⟶ Y) :
    MWProj.map f = f.hom.baseHom.op := rfl

/-! ## 3. MW is a CFG -/

/-! ### 3.1 Base-change morphism in MW -/

/-- The base-change morphism in `MW`: given `f : R' ⟶ R` and `W'` elliptic over `R'`,
the source `⟨R, W'.map f.hom⟩` is elliptic by `isElliptic_map`. -/
def mwBaseChangeHom {R R' : CommRingCat.{u}} (f : R' ⟶ R) (W' : WeierstrassCurve R')
    [hW' : W'.IsElliptic] :
    (⟨⟨R, W'.map f.hom⟩, isElliptic_map W' f.hom⟩ : MW.{u}) ⟶
    ⟨⟨R', W'⟩, hW'⟩ :=
  ObjectProperty.homMk (baseChangeHom f W')

@[simp] lemma mwBaseChangeHom_hom {R R' : CommRingCat.{u}} (f : R' ⟶ R)
    (W' : WeierstrassCurve R') [W'.IsElliptic] :
    (mwBaseChangeHom f W').hom = baseChangeHom f W' := rfl

@[simp] lemma MWProj_map_mwBaseChangeHom {R R' : CommRingCat.{u}} (f : R' ⟶ R)
    (W' : WeierstrassCurve R') [W'.IsElliptic] :
    MWProj.map (mwBaseChangeHom f W') = f.op := rfl

/-! ### 3.2 HomLift for MWProj -/

instance MWProj_isHomLift (X Y : MW.{u}) (φ : X ⟶ Y) :
    MWProj.IsHomLift (MWProj.map φ) φ := inferInstance

instance mwBaseChangeHom_isHomLift {R R' : CommRingCat.{u}} (f : R' ⟶ R)
    (W' : WeierstrassCurve R') [W'.IsElliptic] :
    MWProj.IsHomLift f.op (mwBaseChangeHom f W') := by
  change MWProj.IsHomLift (MWProj.map (mwBaseChangeHom f W')) _
  exact inferInstance

/-! ### 3.3 mwBaseChangeHom is strongly Cartesian -/

/-- `mwBaseChangeHom f W'` is strongly Cartesian over `f.op` for `MWProj`.
The proof mirrors `baseChangeHom_isStronglyCartesian` in `Fibered.lean`, using
the full faithfulness of `ellipticProp.ι` to transfer uniqueness from `𝒲` to `MW`. -/
instance mwBaseChangeHom_isStronglyCartesian {R R' : CommRingCat.{u}} (f : R' ⟶ R)
    (W' : WeierstrassCurve R') [W'.IsElliptic] :
    MWProj.IsStronglyCartesian f.op (mwBaseChangeHom f W') where
  universal_property' := by
    intro ⟨⟨A, V⟩, hV⟩ (g : op A ⟶ op R) ψ hψ
    have hk_op : ψ.hom.baseHom.op = g ≫ f.op := by
      have h := @IsHomLift.fac' _ _ _ _ MWProj _ _ _ _ (g ≫ f.op) ψ hψ
      simp only [MWProj, Functor.comp_map, proj_map, ObjectProperty.ι_map] at h
      exact h
    have hk_eq : ψ.hom.baseHom = f ≫ g.unop := by
      apply_fun Quiver.Hom.unop at hk_op
      rw [Quiver.Hom.unop_op, unop_comp, Quiver.Hom.unop_op] at hk_op
      exact hk_op
    have hcond : ψ.hom.vc • V = (W'.map f.hom).map g.unop.hom := by
      have h := ψ.hom.cond
      rw [hk_eq, CommRingCat.hom_comp, ← WeierstrassCurve.map_map] at h
      exact h
    let χ : (⟨⟨A, V⟩, hV⟩ : MW) ⟶ ⟨⟨R, W'.map f.hom⟩, isElliptic_map W' f.hom⟩ :=
      ObjectProperty.homMk ⟨g.unop, ψ.hom.vc, hcond⟩
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- χ lifts g through MWProj
      change MWProj.IsHomLift (MWProj.map χ) _
      exact inferInstance
    · -- χ ≫ mwBaseChangeHom = ψ
      apply ObjectProperty.hom_ext
      apply Hom.ext
      · change f ≫ g.unop = ψ.hom.baseHom
        exact hk_eq.symm
      · change (baseChangeHom f W').vc.map g.unop.hom * ψ.hom.vc = ψ.hom.vc
        simp [baseChangeHom]
    · -- Uniqueness
      intro χ' ⟨hχ', hχ'comp⟩
      apply ObjectProperty.hom_ext
      apply Hom.ext
      · have hj_eq : χ'.hom.baseHom = g.unop := by
          have h := @IsHomLift.eq_of_isHomLift _ _ _ _ MWProj
              ⟨⟨A, V⟩, hV⟩ ⟨⟨R, W'.map f.hom⟩, isElliptic_map W' f.hom⟩ g χ' hχ'
          simp only [MWProj, Functor.comp_map, proj_map, ObjectProperty.ι_map] at h
          have h2 := congr_arg Quiver.Hom.unop h
          simpa [Quiver.Hom.unop_op] using h2.symm
        exact hj_eq
      · have h := congr_arg (fun m => m.hom.vc) hχ'comp
        simp only [show (χ' ≫ mwBaseChangeHom f W').hom.vc =
            (baseChangeHom f W').vc.map χ'.hom.baseHom.hom * χ'.hom.vc from rfl,
          show (baseChangeHom f W').vc = 1 from rfl,
          WeierstrassCurve.VariableChange.map_one, one_mul] at h
        exact h

private lemma mwBaseChange_sc {R' : CommRingCat.{u}} (W' : WeierstrassCurve R')
    [W'.IsElliptic] (S : CommRingCatᵒᵖ) (g : S ⟶ op R') :
    MWProj.IsStronglyCartesian g (mwBaseChangeHom g.unop W') :=
  Quiver.Hom.op_unop g ▸ @mwBaseChangeHom_isStronglyCartesian _ _ g.unop W' ‹_›

/-! ### 3.4 MWProj is prefibered and fibered -/

instance MWProj_isPreFibered : MWProj.IsPreFibered where
  exists_isCartesian' := by
    intro ⟨⟨R', W'⟩, hW'⟩ S f
    letI hE : W'.IsElliptic := hW'
    exact ⟨⟨⟨S.unop, W'.map f.unop.hom⟩, @isElliptic_map _ _ W' hE _ _ f.unop.hom⟩,
      @mwBaseChangeHom _ _ f.unop W' hE,
      (@mwBaseChange_sc _ W' hE S f).isCartesian_of_isStronglyCartesian⟩

instance MWProj_isFibered : MWProj.IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun ⟨⟨R', W'⟩, hW'⟩ S f => by
    letI hE : W'.IsElliptic := hW'
    exact ⟨⟨⟨S.unop, W'.map f.unop.hom⟩, @isElliptic_map _ _ W' hE _ _ f.unop.hom⟩,
      @mwBaseChangeHom _ _ f.unop W' hE,
      @mwBaseChange_sc _ W' hE S f⟩

/-! ### 3.5 Each fibre of MWProj is a groupoid -/

/-- Every fiber `MWProj.Fiber (op R)` is a groupoid, making `MW` a CFG.
A fiber morphism has `baseHom = 𝟙 R`; the inverse is built with `vc⁻¹`. -/
instance MWProj_fiber_isGroupoid (R : CommRingCat.{u}) :
    IsGroupoid (MWProj.Fiber (op R)) where
  all_isIso := by
    intro X Y f
    obtain ⟨⟨⟨XB, XC⟩, hXC⟩, hX⟩ := X
    obtain ⟨⟨⟨YB, YC⟩, hYC⟩, hY⟩ := Y
    obtain ⟨φ, hφ⟩ := f
    simp only [MWProj, Functor.comp_obj, proj_obj] at hX hY
    have hXR : XB = R := op_injective (show op XB = op R from hX)
    have hYR : YB = R := op_injective (show op YB = op R from hY)
    cases hXR; cases hYR
    have hbase : φ.hom.baseHom = 𝟙 R := by
      -- Use eq_of_isHomLift: for f : MWProj.obj a ⟶ MWProj.obj b, gives f = MWProj.map φ
      have h : φ.hom.baseHom.op = 𝟙 (op R) := by
        have heq := @IsHomLift.eq_of_isHomLift _ _ _ _ MWProj
            ⟨⟨R, XC⟩, hXC⟩ ⟨⟨R, YC⟩, hYC⟩
            (𝟙 (op R) : MWProj.obj ⟨⟨R, XC⟩, hXC⟩ ⟶ MWProj.obj ⟨⟨R, YC⟩, hYC⟩) φ hφ
        simp only [MWProj, Functor.comp_map, proj_map, ObjectProperty.ι_map] at heq
        exact heq.symm
      apply_fun Quiver.Hom.unop at h
      simpa [Quiver.Hom.unop_op] using h
    have hcond : φ.hom.vc • XC = YC := by
      have h := φ.hom.cond
      rw [hbase] at h
      simpa [WeierstrassCurve.map_id] using h
    let ψ_hom : (⟨R, YC⟩ : Weierstrass.{u}) ⟶ ⟨R, XC⟩ := {
      baseHom := 𝟙 R
      vc := φ.hom.vc⁻¹
      cond := by
        rw [CommRingCat.hom_id, WeierstrassCurve.map_id]
        calc φ.hom.vc⁻¹ • YC
            = φ.hom.vc⁻¹ • (φ.hom.vc • XC) := congrArg (φ.hom.vc⁻¹ • ·) hcond.symm
          _ = XC := inv_smul_smul _ _
    }
    let ψ : (⟨⟨R, YC⟩, hYC⟩ : MW) ⟶ ⟨⟨R, XC⟩, hXC⟩ := ObjectProperty.homMk ψ_hom
    have hψ_vert : MWProj.IsHomLift (𝟙 (op R)) ψ := by
      have h : MWProj.map ψ = 𝟙 (op R) := by
        simp [MWProj, ψ, ψ_hom]
      rw [← h]; exact .map ψ
    refine ⟨⟨⟨ψ, hψ_vert⟩,
      Functor.Fiber.hom_ext (show φ ≫ ψ = 𝟙 (⟨⟨R, XC⟩, hXC⟩ : MW) from ?_),
      Functor.Fiber.hom_ext (show ψ ≫ φ = 𝟙 (⟨⟨R, YC⟩, hYC⟩ : MW) from ?_)⟩⟩
    · apply ObjectProperty.hom_ext
      apply Hom.ext
      · change ψ_hom.baseHom ≫ φ.hom.baseHom = 𝟙 R; simp [ψ_hom, hbase]
      · change ψ_hom.vc.map φ.hom.baseHom.hom * φ.hom.vc = 1
        simp [ψ_hom, hbase, CommRingCat.hom_id, WeierstrassCurve.VariableChange.map_id,
          inv_mul_cancel]
    · apply ObjectProperty.hom_ext
      apply Hom.ext
      · change φ.hom.baseHom ≫ ψ_hom.baseHom = 𝟙 R; simp [ψ_hom, hbase]
      · change φ.hom.vc.map ψ_hom.baseHom.hom * ψ_hom.vc = 1
        simp [ψ_hom, CommRingCat.hom_id, WeierstrassCurve.VariableChange.map_id, mul_inv_cancel]

/-! ## 4. j-invariant facts (Blueprint 4.9–4.11) -/

section JInvariant

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- Blueprint 4.9/4.10: The j-invariant is invariant under variable changes.
Re-exposes `WeierstrassCurve.variableChange_j` (VariableChange.lean:246).
j is constant on MW-fibres, giving well-definedness of the j-map on objects. -/
lemma variableChange_j_MW (C : WeierstrassCurve.VariableChange R) :
    (C • W).j = W.j :=
  variableChange_j W C

/-- Blueprint 4.11: The j-invariant is natural under base change.
Re-exposes `WeierstrassCurve.map_j` (Weierstrass.lean:470).
j commutes with base change, giving well-definedness of the j-map on morphisms. -/
lemma map_j_MW {A : Type u} [CommRing A] (f : RingHom R A) :
    (W.map f).j = f W.j :=
  WeierstrassCurve.map_j W f

end JInvariant

end AlgebraicGeometry.EllipticCurve.Moduli