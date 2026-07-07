import GrothendieckCoherence.Moduli.Moduli
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.CategoryTheory.Action

/-!
# Quotient presentation `ℳ^W ≃ [Spec A / G]` (Blueprint §4.3, milestone M4)

Following Blueprint §4.3, we construct the universal Weierstrass curve and identify its
base ring `A = P[ΔP⁻¹]` as the universal localisation, and prove the bijection
between `A`-points and elliptic curves (ring-theoretic content of `ℳ^W ≃ [Spec A / G]`).

## Main results

1. `P`    — universal polynomial ring `ℤ[a₁,a₂,a₃,a₄,a₆]` (Blueprint Def 4.15).
2. `WP`   — tautological Weierstrass curve over `P` (Blueprint Def 4.16).
3. `ΔP`   — discriminant `WP.Δ ∈ P`.
4. `A`    — `Localization.Away ΔP` (Blueprint Def 4.17).
5. `ι`    — structure map `algebraMap P A` (Blueprint Def 4.17).
6. `Wuniv` — universal elliptic curve `WP.map ι` over `A` (Blueprint Def 4.18).
7. `Wuniv_isElliptic` — `Wuniv.IsElliptic` (Blueprint Lemma 4.19).
8. `ringHomEquivElliptic` — bijection `(A →+* R) ≃ {W : WeierstrassCurve R // W.IsElliptic}`
   (Blueprint Lemma 4.24); both `left_inv` and `right_inv` are proved.

## Mathlib API used

- `MvPolynomial.eval₂Hom`            — ring map from `R →+* S` and `σ → S`.
- `MvPolynomial.eval₂Hom_X'`         — `eval₂Hom f g (X i) = g i`.
- `MvPolynomial.eval₂Hom_C`          — `eval₂Hom f g (C r) = f r`.
- `MvPolynomial.ringHom_ext`          — uniqueness for maps out of `MvPolynomial`.
- `WeierstrassCurve.map_Δ`            — `(W.map f).Δ = f W.Δ`.
- `WeierstrassCurve.map_map`          — `(W.map f).map g = W.map (g.comp f)`.
- `WeierstrassCurve.isUnit_Δ`         — `W.Δ` is a unit when `W.IsElliptic`.
- `IsLocalization.Away.algebraMap_isUnit` — `algebraMap R S x` is a unit in `Away x S`.
- `IsLocalization.Away.lift`          — universal map `Away x S →+* P` when `g x` is a unit.
- `IsLocalization.Away.lift_eq`       — `(lift hg) (algebraMap R S a) = g a`.
- `IsLocalization.Away.lift_comp`     — `(lift hg) ∘ algebraMap = g`.
- `IsLocalization.ringHom_ext`        — uniqueness for maps out of a localization.

## Item 6: Missing API for the full `MW ≃ [Spec A / G]`

The full equivalence of CFGs requires:
(a) A construction of `[Spec A / G]` for `G = VariableChange` acting on `A` — not in Mathlib.
(b) `FiberedFunctor` type + `equiv_of_fiberwise_equiv` — not in Mathlib.
(c) Naturality of `ringHomEquivElliptic` and `VariableChange`-equivariance.

The fibrewise content (`fiberEquivAPoints`, `fiber_morph_is_variableChange`) is fully proved.
-/

open WeierstrassCurve MvPolynomial IsLocalization CategoryTheory

universe u

namespace AlgebraicGeometry.EllipticCurve.Moduli

open Weierstrass

/-! ## 1. Universal polynomial ring `P` (Blueprint Def 4.15) -/

/-- The universal polynomial ring `ℤ[X 0, …, X 4]` with five indeterminates
playing the roles of the Weierstrass coefficients `a₁, a₂, a₃, a₄, a₆`. -/
abbrev P : Type := MvPolynomial (Fin 5) ℤ

/-! ## 2. Tautological Weierstrass curve `WP` over `P` (Blueprint Def 4.16) -/

/-- The tautological Weierstrass curve over `P`: the five coefficients are the five
polynomial generators `X 0, …, X 4`. -/
noncomputable def WP : WeierstrassCurve P where
  a₁ := X 0
  a₂ := X 1
  a₃ := X 2
  a₄ := X 3
  a₆ := X 4

/-! ## 3. Discriminant `ΔP`, universal base ring `A`, structure map `ι` (Blueprint Defs 4.17–18) -/

/-- The discriminant polynomial `ΔP = WP.Δ ∈ P`. -/
noncomputable def ΔP : P := WP.Δ

/-- The universal base ring `A = P[ΔP⁻¹] = Localization.Away ΔP`. -/
abbrev A : Type := Localization.Away ΔP

/-- The structure map `ι : P →+* A` = `algebraMap P A`. -/
noncomputable def ι : P →+* A := algebraMap P A

/-- The universal Weierstrass curve `Wuniv = WP.map ι` over `A` (Blueprint Def 4.18). -/
noncomputable def Wuniv : WeierstrassCurve A := WP.map ι

/-! ## 4. `Wuniv.IsElliptic` (Blueprint Lemma 4.19) -/

/-- `Wuniv.Δ = ι ΔP` by `WeierstrassCurve.map_Δ`. -/
lemma Wuniv_Δ_eq : Wuniv.Δ = ι ΔP := WP.map_Δ ι

/-- `ι ΔP` is a unit in `A = Localization.Away ΔP`
(by `IsLocalization.Away.algebraMap_isUnit`). -/
lemma ι_ΔP_isUnit : IsUnit (ι ΔP) :=
  IsLocalization.Away.algebraMap_isUnit ΔP

/-- Blueprint Lemma 4.19: the universal curve `Wuniv` is elliptic over `A`. -/
instance Wuniv_isElliptic : Wuniv.IsElliptic :=
  ⟨Wuniv_Δ_eq ▸ ι_ΔP_isUnit⟩

/-! ## 5. Ring-hom ↔ elliptic curve bijection (Blueprint Lemma 4.24) -/

section RingHomEquivElliptic

variable (R : Type u) [CommRing R]

/-! ### Forward direction: `φ : A →+* R` gives `Wuniv.map φ` -/

/-- Pull back the universal curve along `φ : A →+* R`. -/
noncomputable def toEllipticCurve (φ : A →+* R) : WeierstrassCurve R := Wuniv.map φ

/-- The pulled-back curve is elliptic (ellipticity is stable under base change).
`Wuniv.IsElliptic` and `WeierstrassCurve.map` preserve `IsElliptic`. -/
instance toEllipticCurve_isElliptic (φ : A →+* R) : (toEllipticCurve R φ).IsElliptic := by
  unfold toEllipticCurve
  -- (Wuniv.map φ).Δ = φ Wuniv.Δ = φ (ι ΔP); the latter is a unit since ι_ΔP_isUnit is.
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, Wuniv_Δ_eq]
  exact ι_ΔP_isUnit.map φ

/-! ### Backward direction: elliptic curve over `R` gives `A →+* R` -/

/-- The ring map `P →+* R` sending each generator `X i` to the `i`-th Weierstrass coefficient.
`coeffFun W : Fin 5 → R` satisfies `coeffFun W 0 = W.a₁`, …, `coeffFun W 4 = W.a₆`. -/
noncomputable def coeffFun (W : WeierstrassCurve R) : Fin 5 → R :=
  fun i => Fin.cases W.a₁ (fun i => Fin.cases W.a₂ (fun i =>
    Fin.cases W.a₃ (fun i => Fin.cases W.a₄ (fun _ => W.a₆) i) i) i) i

/-- The ring map `P →+* R` sending generators to the five Weierstrass coefficients of `W`. -/
noncomputable def coeffHom (W : WeierstrassCurve R) : P →+* R :=
  eval₂Hom (Int.castRingHom R) (coeffFun R W)

/-- `WP.map (coeffHom R W) = W`: the universal property of `WP`. -/
lemma WP_map_coeffHom (W : WeierstrassCurve R) : WP.map (coeffHom R W) = W := by
  ext <;>
    simp only [WP, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, coeffHom, eval₂Hom_X']
  -- `coeffFun R W 0 = W.a₁` etc. are definitionally true by `Fin.cases`.
  · rfl  -- a₁: coeffFun R W 0 = W.a₁
  · rfl  -- a₂: coeffFun R W 1 = W.a₂
  · rfl  -- a₃: coeffFun R W 2 = W.a₃
  · rfl  -- a₄: coeffFun R W 3 = W.a₄
  · rfl  -- a₆: coeffFun R W 4 = W.a₆

/-- `coeffHom R W ΔP = W.Δ`. -/
lemma coeffHom_ΔP (W : WeierstrassCurve R) : coeffHom R W ΔP = W.Δ := by
  have := WP.map_Δ (coeffHom R W)
  rw [WP_map_coeffHom] at this
  exact this.symm

/-- `coeffHom R W ΔP` is a unit when `W.IsElliptic`. -/
lemma isUnit_coeffHom_ΔP (W : WeierstrassCurve R) [W.IsElliptic] :
    IsUnit (coeffHom R W ΔP) := by
  rw [coeffHom_ΔP]; exact W.isUnit_Δ

/-- Lift `coeffHom R W` to `A = P[ΔP⁻¹] →+* R` via the localization universal property.
Uses `IsLocalization.Away.lift`. -/
noncomputable def fromEllipticCurve (W : WeierstrassCurve R) [W.IsElliptic] : A →+* R :=
  IsLocalization.Away.lift ΔP (isUnit_coeffHom_ΔP R W)

/-- `fromEllipticCurve R W` composed with `ι` equals `coeffHom R W`
(by `IsLocalization.Away.lift_comp`). -/
@[simp] lemma fromEllipticCurve_comp (W : WeierstrassCurve R) [W.IsElliptic] :
    (fromEllipticCurve R W).comp ι = coeffHom R W :=
  IsLocalization.Away.lift_comp ΔP (isUnit_coeffHom_ΔP R W)

/-- `fromEllipticCurve R W (ι p) = coeffHom R W p`
(by `IsLocalization.Away.lift_eq`). -/
@[simp] lemma fromEllipticCurve_ι (W : WeierstrassCurve R) [W.IsElliptic] (p : P) :
    fromEllipticCurve R W (ι p) = coeffHom R W p :=
  IsLocalization.Away.lift_eq ΔP (isUnit_coeffHom_ΔP R W) p

/-! ### The full bijection -/

/-- **Blueprint Lemma 4.24**: natural bijection
`(A →+* R) ≃ {W : WeierstrassCurve R // W.IsElliptic}`.
Both `left_inv` and `right_inv` are fully proved. -/
noncomputable def ringHomEquivElliptic :
    (A →+* R) ≃ {W : WeierstrassCurve R // W.IsElliptic} where
  toFun φ := ⟨toEllipticCurve R φ, toEllipticCurve_isElliptic R φ⟩
  invFun := fun ⟨W, hW⟩ => @fromEllipticCurve R _ W hW
  left_inv := by
    intro φ
    -- By `IsLocalization.ringHom_ext`, it suffices to show both maps agree on `algebraMap P A`.
    apply IsLocalization.ringHom_ext (M := Submonoid.powers ΔP)
    -- Goal: (fromEllipticCurve R (Wuniv.map φ)).comp (algebraMap P A) = φ.comp (algebraMap P A)
    -- LHS = coeffHom R (Wuniv.map φ) by fromEllipticCurve_comp
    -- Use `change` to rewrite `algebraMap P A` as `ι`.
    change (fromEllipticCurve R (Wuniv.map φ)).comp ι = φ.comp ι
    rw [fromEllipticCurve_comp]
    -- Both are ring maps `P →+* R`; check by `MvPolynomial.ringHom_ext`.
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [coeffHom, ι]
    · intro i
      -- Goal: coeffHom R (Wuniv.map φ) (X i) = (φ.comp ι) (X i)
      -- LHS = coeffFun R (Wuniv.map φ) i, RHS = φ (ι (X i)) = φ (algebraMap P A (X i))
      simp only [coeffHom, eval₂Hom_X', RingHom.comp_apply, ι]
      -- After fin_cases, `i` is concrete; `coeffFun R W j` for concrete `j` reduces definitionally.
      fin_cases i <;>
        simp only [Wuniv, WP, WeierstrassCurve.map, coeffFun] <;> rfl
  right_inv := by
    intro ⟨W, hW⟩
    apply Subtype.val_injective
    simp only [toEllipticCurve, Wuniv, WeierstrassCurve.map_map]
    -- Goal: WP.map ((fromEllipticCurve R W).comp ι) = W
    rw [fromEllipticCurve_comp, WP_map_coeffHom]

end RingHomEquivElliptic

/-! ## 6. Variable-change action on `A`-points (transported through `ringHomEquivElliptic`) -/

section VariableChangeAction

variable (R : Type u) [CommRing R]

/-- The `VariableChange R`-action on `{W : WeierstrassCurve R // W.IsElliptic}` lifted from
the `MulAction (VariableChange R) (WeierstrassCurve R)` using `isElliptic_variableChange`. -/
instance smulElliptic : SMul (WeierstrassCurve.VariableChange R)
    {W : WeierstrassCurve R // W.IsElliptic} :=
  ⟨fun C ⟨W, _hW⟩ => ⟨C • W, inferInstance⟩⟩

@[simp] lemma smulElliptic_val (C : WeierstrassCurve.VariableChange R)
    (W : {W : WeierstrassCurve R // W.IsElliptic}) :
    (C • W).val = C • W.val := rfl

/-- The `VariableChange R`-action on the elliptic subtype is a `MulAction`. -/
instance mulActionElliptic : MulAction (WeierstrassCurve.VariableChange R)
    {W : WeierstrassCurve R // W.IsElliptic} where
  one_smul W := by
    ext1
    simp [smulElliptic_val, one_smul]
  mul_smul C C' W := by
    ext1
    simp [smulElliptic_val, mul_smul]

/-- The `VariableChange R`-action on ring maps `A →+* R`, transported through
`ringHomEquivElliptic R : (A →+* R) ≃ {W : WeierstrassCurve R // W.IsElliptic}`.
Concretely: `C • φ = fromEllipticCurve R (C • toEllipticCurve R φ)`. -/
noncomputable instance smulRingHom : SMul (WeierstrassCurve.VariableChange R) (A →+* R) :=
  ⟨fun C φ => (ringHomEquivElliptic R).symm (C • ringHomEquivElliptic R φ)⟩

@[simp] lemma smulRingHom_def (C : WeierstrassCurve.VariableChange R) (φ : A →+* R) :
    C • φ = (ringHomEquivElliptic R).symm (C • ringHomEquivElliptic R φ) := rfl

/-- **Blueprint §4.3**: the `VariableChange R`-action on `A →+* R` is a `MulAction`.
The laws follow formally from `mulActionElliptic` and bijectivity of `ringHomEquivElliptic`. -/
noncomputable instance mulActionRingHom :
    MulAction (WeierstrassCurve.VariableChange R) (A →+* R) where
  one_smul φ := by
    simp [smulRingHom_def, one_smul, Equiv.symm_apply_apply]
  mul_smul C C' φ := by
    simp [smulRingHom_def, mul_smul, Equiv.apply_symm_apply]

end VariableChangeAction

/-! ## 7. Quotient presentation (Blueprint Thm 4.31) -/

section QuotientPresentation

variable {R : CommRingCat.{u}}

/-- **Blueprint Thm 4.31, fibrewise objects**: Objects of `MWProj.Fiber (op R)` biject with
ring maps `A →+* R` (i.e. `A`-points of `Spec R`), via `ringHomEquivElliptic`.

An object of `MWProj.Fiber (op R)` is a pair `⟨obj : MW, hobj : MWProj.obj obj = op R⟩`,
i.e. `⟨⟨⟨R, W⟩, hW⟩, rfl⟩` for `W : WeierstrassCurve R` with `W.IsElliptic`. -/
noncomputable def fiberEquivAPoints :
    MWProj.Fiber (Opposite.op R) ≃ (A →+* R) :=
  -- Step 1: MWProj.Fiber (op R) ≃ {W : WeierstrassCurve R // W.IsElliptic}
  ({ toFun := fun X => by
       obtain ⟨⟨⟨XB, XC⟩, hXC⟩, hX⟩ := X
       simp only [MWProj, Functor.comp_obj, proj_obj] at hX
       exact Opposite.op_injective hX ▸ (⟨XC, hXC⟩ : {W : WeierstrassCurve XB // W.IsElliptic})
     invFun := fun ⟨W, hW⟩ => ⟨⟨⟨R, W⟩, hW⟩, rfl⟩
     left_inv := by
       intro ⟨⟨⟨XB, XC⟩, hXC⟩, hX⟩
       simp only [MWProj, Functor.comp_obj, proj_obj] at hX
       have hXR : XB = R := Opposite.op_injective hX
       cases hXR; rfl
     right_inv := fun _ => rfl } :
      MWProj.Fiber (Opposite.op R) ≃ {W : WeierstrassCurve R // W.IsElliptic})
  -- Step 2: {W // IsElliptic} ≃ (A →+* R) via ringHomEquivElliptic.symm
  |>.trans (ringHomEquivElliptic R).symm

/-- **Blueprint Thm 4.31, fibrewise morphisms**: For `f : X ⟶ Y` in `MWProj.Fiber (op R)`,
the underlying MW morphism `f.val` lies over `𝟙 (op R)` — this is exactly the fiber condition
`f.2 : IsHomLift MWProj (𝟙 (op R)) f.val`.

The Weierstrass compatibility condition is `vc • X.curve = Y.curve.map baseHom` (`f.val.hom.cond`).
Together these identify fiber morphisms with variable changes over `𝟙 R`, giving the morphism part
of `MW ≃ [Spec A / VariableChange]` (Blueprint Thm 4.31). -/
lemma fiber_morph_is_variableChange
    {X Y : MWProj.Fiber (Opposite.op R)}
    (f : X ⟶ Y) :
    f.val.hom.vc • X.val.obj.curve =
      Y.val.obj.curve.map f.val.hom.baseHom.hom :=
  f.val.hom.cond

/-!
### Documented sorry for the full CFG equivalence (Blueprint Thm 4.31)

The full statement `MW ≃ [Spec A / VariableChange]` as an equivalence of CFGs requires
Mathlib API that does not yet exist:
(a) **Quotient-stack CFG**: no construction of `[Spec A / G]` as a fibered category over `Aff`
    for the group `G = VariableChange` acting on `A`.
(b) **FiberedFunctor**: no `FiberedFunctor` type or `equiv_of_fiberwise_equiv` to assemble a
    fiberwise equivalence and naturality data into a full CFG-equivalence.
(c) **Equivariance**: no proof that `ringHomEquivElliptic` is natural in `R` and compatible
    with the `VariableChange`-actions on both sides in a functorial way.

The fibrewise content is proved in `fiberEquivAPoints` (objects) and
`fiber_morph_is_variableChange` (morphisms).  The action of §6 (`mulActionRingHom`) supplies
the equivariance data at each fibre.
-/

/-- **Blueprint Thm 4.31, fibrewise action-groupoid equivalence (sorry: deferred)**:
The fibre groupoid `MWProj.Fiber (op R)` is equivalent, as a category, to the action groupoid
`ActionCategory (VariableChange R) (A →+* R)` of the variable-change group acting on `A`-points.

The proof packages:
- **objects**: `fiberEquivAPoints` (Blueprint Thm 4.31 objects), an equivalence
  `MWProj.Fiber (op R) ≃ (A →+* R)` implemented via `ringHomEquivElliptic`.
- **morphisms**: `fiber_morph_is_variableChange` identifies fiber morphisms `f : X ⟶ Y` with
  variable changes `vc` satisfying `vc • X.curve = Y.curve.map f.baseHom`.
- **action**: `mulActionRingHom` from §6, transporting the `VariableChange`-action on
  `{W // IsElliptic}` to `A →+* R` via `ringHomEquivElliptic`.

The global equivalence `MW ≃ [Spec A / VariableChange]` further needs quotient-stack CFG
construction and FiberedFunctor API absent from Mathlib; see the module docstring. -/
noncomputable def MW_fiber_equiv_actionGroupoid (R : CommRingCat.{u}) :
    MWProj.Fiber (Opposite.op R) ≌
      CategoryTheory.ActionCategory (WeierstrassCurve.VariableChange R) (A →+* R) := by
  sorry

end QuotientPresentation

end AlgebraicGeometry.EllipticCurve.Moduli
