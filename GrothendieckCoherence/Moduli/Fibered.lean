import GrothendieckCoherence.Moduli.Weierstrass
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Groupoid

/-!
# Fibered-category structure of `𝒲` (Blueprint §3, milestone M2)

We prove that `proj : Weierstrass ⥤ CommRingCatᵒᵖ` is a fibered category
(a "category fibered in groupoids", CFG).

## Main results

1. `proj_isHomLift` : every `φ : X ⟶ Y` satisfies `proj.IsHomLift (proj.map φ) φ`.

2. `baseChangeHom` : for `f : R' ⟶ R` and `W' : WeierstrassCurve R'`, the morphism
   `⟨R, W'.map f.hom⟩ ⟶ ⟨R', W'⟩` with `baseHom = f` and `vc = 1`.

3. `baseChangeHom_isStronglyCartesian` : `baseChangeHom f W'` is strongly Cartesian
   over `f.op` via `Functor.IsStronglyCartesian`.

4. `proj_isFibered` : `proj` is a fibered category (`Functor.IsFibered`),
   via `IsFibered.of_exists_isStronglyCartesian`.

5. `proj_fiber_isGroupoid` : every fiber `proj.Fiber (op R)` is a groupoid
   (`IsGroupoid`), making `𝒲` a CFG.

## Exact Mathlib FiberedCategory API names used
- `CategoryTheory.Functor.IsHomLift`           (HomLift.lean, via Cartesian)
- `CategoryTheory.Functor.IsStronglyCartesian` (Cartesian.lean)
- `CategoryTheory.Functor.IsPreFibered`        (Fibered.lean)
- `CategoryTheory.Functor.IsFibered`           (Fibered.lean)
- `CategoryTheory.Functor.Fiber`               (Fiber.lean)
- `CategoryTheory.IsGroupoid`                  (Groupoid.lean)
-/

open CategoryTheory WeierstrassCurve Opposite

namespace AlgebraicGeometry.EllipticCurve.Moduli

open Weierstrass

universe u

/-! ## 1. HomLift: every morphism lifts its own base arrow -/

/-- Every morphism `φ : X ⟶ Y` in `𝒲` satisfies `proj.IsHomLift (proj.map φ) φ`.
Since `proj.map φ = φ.baseHom.op`, this says `φ` lifts its own base arrow. -/
instance proj_isHomLift (X Y : Weierstrass.{u}) (φ : X ⟶ Y) :
    proj.IsHomLift (proj.map φ) φ := inferInstance

/-! ## 2. Base-change morphism -/

variable {R R' : CommRingCat.{u}} (f : R' ⟶ R) (W' : WeierstrassCurve R')

/-- The base-change morphism `λ_{f,W'} : ⟨R, W'.map f.hom⟩ ⟶ ⟨R', W'⟩`.
It has `baseHom = f` and `vc = 1`; the compatibility condition holds by `one_smul`. -/
def baseChangeHom : (⟨R, W'.map f.hom⟩ : Weierstrass.{u}) ⟶ ⟨R', W'⟩ where
  baseHom := f
  vc := 1
  cond := by simp

@[simp] lemma baseChangeHom_baseHom : (baseChangeHom f W').baseHom = f := rfl
@[simp] lemma baseChangeHom_vc : (baseChangeHom f W').vc = 1 := rfl

/-- `proj` maps `baseChangeHom f W'` to `f.op`. -/
@[simp] lemma proj_map_baseChangeHom : proj.map (baseChangeHom f W') = f.op := rfl

/-! ## 3. HomLift instance for baseChangeHom -/

/-- `baseChangeHom f W'` lifts `f.op` through `proj`. -/
instance baseChangeHom_isHomLift : proj.IsHomLift f.op (baseChangeHom f W') := by
  change proj.IsHomLift (proj.map (baseChangeHom f W')) _; exact inferInstance

/-! ## 4. Strongly Cartesian -/

/-- `baseChangeHom f W'` is strongly Cartesian over `f.op`.

**Universal property (blueprint §3.3)**: given `⟨A, V⟩ : 𝒲`, a base morphism
`g : op A ⟶ op R` and `ψ : ⟨A, V⟩ ⟶ ⟨R', W'⟩` with
`proj.IsHomLift (g ≫ f.op) ψ`, the unique factorisation through `baseChangeHom f W'`
is `χ = ⟨g.unop, ψ.vc, _⟩`; vc is unchanged because `baseChangeHom.vc = 1`. -/
instance baseChangeHom_isStronglyCartesian :
    proj.IsStronglyCartesian f.op (baseChangeHom f W') where
  universal_property' := by
    -- Introduce g with explicit type so g.unop and unop_comp typecheck correctly.
    intro ⟨A, V⟩ (g : op A ⟶ op R) ψ hψ
    -- From hψ: proj.map ψ = g ≫ f.op, i.e. ψ.baseHom.op = g ≫ f.op
    -- Use fac' with explicit instance to avoid subst_hom_lift issues
    have hk_op : ψ.baseHom.op = g ≫ f.op := by
      have h := @IsHomLift.fac' _ _ _ _ proj _ _ _ _ (g ≫ f.op) ψ hψ
      simp only [proj_map] at h
      exact h
    -- ψ.baseHom = f ≫ g.unop: unop both sides
    have hk_eq : ψ.baseHom = f ≫ g.unop := by
      apply_fun Quiver.Hom.unop at hk_op
      rw [Quiver.Hom.unop_op, unop_comp, Quiver.Hom.unop_op] at hk_op
      exact hk_op
    -- cond for χ: ψ.vc • V = (W'.map f.hom).map g.unop.hom
    have hcond : ψ.vc • V = (W'.map f.hom).map g.unop.hom := by
      have h := ψ.cond
      rw [hk_eq, CommRingCat.hom_comp, ← WeierstrassCurve.map_map] at h
      exact h
    refine ⟨⟨g.unop, ψ.vc, hcond⟩, ⟨?_, ?_⟩, ?_⟩
    · -- χ lifts g: proj.map ⟨g.unop, ψ.vc, hcond⟩ = g.unop.op = g
      -- g.unop.op = g by Quiver.Hom.op_unop (which is rfl), so change works
      change proj.IsHomLift (proj.map (⟨g.unop, ψ.vc, hcond⟩ :
          (⟨A, V⟩ : Weierstrass) ⟶ ⟨R, W'.map f.hom⟩)) _
      exact inferInstance
    · -- χ ≫ baseChangeHom = ψ
      apply Hom.ext
      · -- comp baseHom: f ≫ g.unop = ψ.baseHom (Hom.comp_baseHom says ψ_ext.baseHom ≫ χ.baseHom)
        change f ≫ g.unop = ψ.baseHom; exact hk_eq.symm
      · -- comp vc: (baseChangeHom f W').vc.map g.unop.hom * ψ.vc = ψ.vc
        change (baseChangeHom f W').vc.map g.unop.hom * ψ.vc = ψ.vc
        simp [baseChangeHom]
    · -- Uniqueness
      intro χ' ⟨hχ', hχ'comp⟩
      -- χ'.baseHom = g.unop from hχ' using fac' with explicit instance
      have hj_eq : χ'.baseHom = g.unop := by
        -- eq_of_isHomLift needs f : proj.obj a ⟶ proj.obj b; g : op A ⟶ op R works since
        -- proj.obj ⟨A,V⟩ = op A definitionally
        have h := @IsHomLift.eq_of_isHomLift _ _ _ _ proj ⟨A, V⟩ ⟨R, W'.map f.hom⟩ g χ' hχ'
        -- h : g = proj.map χ' = χ'.baseHom.op
        simp only [proj_map] at h
        -- h : g = χ'.baseHom.op; apply unop to get g.unop = χ'.baseHom
        have h2 := congr_arg Quiver.Hom.unop h
        simpa [Quiver.Hom.unop_op] using h2.symm
      -- χ'.vc = ψ.vc from hχ'comp
      have hvc : χ'.vc = ψ.vc := by
        have h := congr_arg Hom.vc hχ'comp
        -- h : (χ' ≫ baseChangeHom f W').vc = ψ.vc
        -- (χ' ≫ baseChangeHom f W').vc = 1.map χ'.baseHom.hom * χ'.vc = χ'.vc
        simp only [show (χ' ≫ baseChangeHom f W').vc =
          (baseChangeHom f W').vc.map χ'.baseHom.hom * χ'.vc from rfl,
          baseChangeHom_vc, WeierstrassCurve.VariableChange.map_one, one_mul] at h
        exact h
      exact Hom.ext hj_eq hvc

/-! ## 5. `proj` is a prefibered and fibered category -/

-- For any g : S ⟶ op R' in CommRingCatᵒᵖ, baseChangeHom g.unop W' is sc over g.
private lemma baseChange_sc (R' : CommRingCat.{u}) (W' : WeierstrassCurve R')
    (S : CommRingCatᵒᵖ) (g : S ⟶ op R') :
    proj.IsStronglyCartesian g (baseChangeHom g.unop W') :=
  -- g.unop.op = g, so this is IsStronglyCartesian (g.unop).op (baseChangeHom g.unop W')
  Quiver.Hom.op_unop g ▸ @baseChangeHom_isStronglyCartesian _ _ g.unop W'

/-- `proj` is prefibered: every base morphism `f : S ⟶ op R'` has a Cartesian lift. -/
instance proj_isPreFibered : proj.IsPreFibered where
  exists_isCartesian' := by
    intro ⟨R', W'⟩ S f
    exact ⟨⟨S.unop, W'.map f.unop.hom⟩, baseChangeHom f.unop W',
      (baseChange_sc R' W' S f).isCartesian_of_isStronglyCartesian⟩

/-- `proj` is fibered via `IsFibered.of_exists_isStronglyCartesian`. -/
instance proj_isFibered : proj.IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun ⟨R', W'⟩ S f =>
    ⟨⟨S.unop, W'.map f.unop.hom⟩, baseChangeHom f.unop W', baseChange_sc R' W' S f⟩

/-! ## 6. Fiber groupoids — 𝒲 is a CFG -/

/-- Every fiber `proj.Fiber (op R)` is a groupoid.

After substituting `X.base = R = Y.base`, a fiber morphism `φ` has `φ.baseHom = 𝟙 R`
(since `𝟙 (op R) = φ.baseHom.op`) and `φ.vc • W = W₀`.
The inverse has `vc = φ.vc⁻¹`. -/
instance proj_fiber_isGroupoid (R : CommRingCat.{u}) :
    IsGroupoid (proj.Fiber (op R)) where
  all_isIso := by
    intro X Y f
    obtain ⟨⟨XB, XC⟩, hX⟩ := X
    obtain ⟨⟨YB, YC⟩, hY⟩ := Y
    obtain ⟨φ, hφ⟩ := f
    -- proj.obj ⟨XB,XC⟩ = op XB definitionally, so type ascription works
    have hXR : XB = R := op_injective (show op XB = op R from hX)
    have hYR : YB = R := op_injective (show op YB = op R from hY)
    cases hXR; cases hYR
    -- Now φ : ⟨R, XC⟩ ⟶ ⟨R, YC⟩ in Weierstrass
    -- φ.baseHom : R ⟶ R, hφ : proj.IsHomLift (𝟙 (op R)) φ
    -- Extract φ.baseHom = 𝟙 R using fac with explicit instance
    have hbase : φ.baseHom = 𝟙 R := by
      have h : (𝟙 (op R) : op R ⟶ op R) = φ.baseHom.op := by
        have := @IsHomLift.fac _ _ _ _ proj _ _ _ _ (𝟙 (op R)) φ hφ
        simpa [proj] using this
      -- unop both sides: 𝟙 R = φ.baseHom
      have h2 := congr_arg Quiver.Hom.unop h
      simp [Quiver.Hom.unop_op] at h2
      exact h2.symm
    -- φ.cond : φ.vc • XC = YC (using hbase and map_id)
    have hcond : φ.vc • XC = YC := by
      have h := φ.cond
      rw [hbase] at h
      simpa [WeierstrassCurve.map_id] using h
    -- Build inverse ψ : ⟨R, YC⟩ ⟶ ⟨R, XC⟩ with vc = φ.vc⁻¹
    let ψ : (⟨R, YC⟩ : Weierstrass.{u}) ⟶ ⟨R, XC⟩ := {
      baseHom := 𝟙 R
      vc := φ.vc⁻¹
      cond := by
        rw [CommRingCat.hom_id, WeierstrassCurve.map_id]
        -- Goal: φ.vc⁻¹ • YC = XC
        -- From hcond: φ.vc • XC = YC
        calc φ.vc⁻¹ • YC = φ.vc⁻¹ • (φ.vc • XC) := congrArg (φ.vc⁻¹ • ·) hcond.symm
          _ = XC := inv_smul_smul _ _
    }
    -- ψ is vertical (lifts 𝟙 (op R))
    have hψ_vert : proj.IsHomLift (𝟙 (op R)) ψ := by
      have h : proj.map ψ = 𝟙 (op R) := by simp [proj, ψ]
      rw [← h]; exact .map ψ
    -- IsIso for ⟨φ, hφ⟩ with explicit inverse ⟨ψ, hψ_vert⟩
    refine ⟨⟨⟨ψ, hψ_vert⟩,
      Functor.Fiber.hom_ext (show φ ≫ ψ = 𝟙 (⟨R, XC⟩ : Weierstrass) from ?_),
      Functor.Fiber.hom_ext (show ψ ≫ φ = 𝟙 (⟨R, YC⟩ : Weierstrass) from ?_)⟩⟩
    · -- φ ≫ ψ = 𝟙 ⟨R, XC⟩
      apply Hom.ext
      · -- baseHom: ψ.baseHom ≫ φ.baseHom = 𝟙 R ≫ 𝟙 R = 𝟙 R
        change ψ.baseHom ≫ φ.baseHom = 𝟙 R; simp [ψ, hbase]
      · -- vc: ψ.vc.map φ.baseHom.hom * φ.vc = φ.vc⁻¹.map (𝟙 R).hom * φ.vc = φ.vc⁻¹ * φ.vc = 1
        change ψ.vc.map φ.baseHom.hom * φ.vc = 1
        simp [ψ, hbase, CommRingCat.hom_id, WeierstrassCurve.VariableChange.map_id, inv_mul_cancel]
    · -- ψ ≫ φ = 𝟙 ⟨R, YC⟩
      apply Hom.ext
      · -- baseHom: φ.baseHom ≫ ψ.baseHom = 𝟙 R ≫ 𝟙 R = 𝟙 R
        change φ.baseHom ≫ ψ.baseHom = 𝟙 R; simp [ψ, hbase]
      · -- vc: φ.vc.map ψ.baseHom.hom * ψ.vc = φ.vc.map (𝟙 R).hom * φ.vc⁻¹ = φ.vc * φ.vc⁻¹ = 1
        change φ.vc.map ψ.baseHom.hom * ψ.vc = 1
        simp [ψ, CommRingCat.hom_id, WeierstrassCurve.VariableChange.map_id, mul_inv_cancel]

end AlgebraicGeometry.EllipticCurve.Moduli
