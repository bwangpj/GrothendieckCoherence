/-
# The moduli stack of elliptic curves (Weierstrass model), via fibered categories

Formalisation following `moduli_ell_blueprint`. Milestones on current Mathlib:

* **M1** Equivariance — supplied by Mathlib (`WeierstrassCurve.map_variableChange` etc.).
* **M2** The fibered category `𝒲` of Weierstrass curves over `Aff = CommRingCatᵒᵖ`,
  its projection, strongly-cartesian base-change arrows, prefibered/fibered
  structure, and groupoid fibres (a CFG). — `Moduli/Weierstrass.lean`, `Moduli/Fibered.lean`.
* **M3** The moduli CFG `ℳ^W_{1,1}` (full subcategory of elliptic objects), its CFG
  structure, and the j-invariant naturality facts. — `Moduli/Moduli.lean`.
* **M4** The quotient presentation: universal ring `P = ℤ[a₁..a₆]`,
  `A = P[Δ⁻¹]`, universal elliptic curve, the bijection
  `(A →+* R) ≃ {elliptic W over R}`, the fibre bijection, and the faithful
  fibre-groupoid ↔ action-groupoid equivalence (proof deferred; the global
  `[Spec A / G]` CFG-equivalence needs quotient-stack API not in Mathlib). —
  `Moduli/Quotient.lean`.
-/
import GrothendieckCoherence.Moduli.Weierstrass
import GrothendieckCoherence.Moduli.Fibered
import GrothendieckCoherence.Moduli.Moduli
import GrothendieckCoherence.Moduli.Quotient
