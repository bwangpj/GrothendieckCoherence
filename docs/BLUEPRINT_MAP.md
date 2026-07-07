# Blueprint ↔ Lean declaration map

Each row: blueprint label (`content.tex`), intended Lean name, module, Stacks tag.
Status `def*` = placeholder definition (`:= sorry` / stub); `thm*` = statement with
`sorry` proof. All will build; none are proved yet.

## WP1 — Quasi-coherent sheaves (Part `qcoh`)

| Label | Lean name | Module | Stacks |
|-------|-----------|--------|--------|
| `con:tilde` | `ModuleCat.tildeFunctor` | `QuasiCoherent/Tilde` | 01I6 |
| `lem:tilde-sections` | `ModuleCat.Tilde.sections_basicOpen`, `stalkIso` | `QuasiCoherent/Tilde` | 01I6 |
| `lem:tilde-ff` | `ModuleCat.tildeFunctor_fullyFaithful`, `_exact` | `QuasiCoherent/Tilde` | 01I6 |
| `prop:affine-equiv` | `AlgebraicGeometry.Spec.qcohEquivModule` | `QuasiCoherent/Tilde` | 01I6 |
| `lem:tilde-functorial` | `Spec.pushforward_tilde`, `pullback_tilde` | `QuasiCoherent/Tilde` | 01I6 |
| `def:qcoh` | `Scheme.Modules.IsQuasicoherent` | `QuasiCoherent/Basic` | 01BD |
| `lem:qcoh-agree` | `Scheme.Modules.isQuasicoherent_iff_sheafOfModules` | `QuasiCoherent/Basic` | 01BG |
| `lem:qcoh-local` | `Scheme.Modules.isQuasicoherent_of_cover` | `QuasiCoherent/Basic` | 01I6 |
| `lem:qcoh-basic` | `Scheme.Modules.isQuasicoherent_pullback` | `QuasiCoherent/Basic` | 01BM |
| `prop:qcoh-abelian` | `Scheme.Modules.qcoh_isAbelian` | `QuasiCoherent/Basic` | 01LA |
| `def:invertible` | `Scheme.Modules.IsInvertible` | `QuasiCoherent/Invertible` | 01CR |
| `lem:tensor-invertible-exact` | `Scheme.Modules.tensorInvertible_exact` | `QuasiCoherent/Invertible` | 01CR |

## WP2 — Cohomology core (Part `cohomology`)

| Label | Lean name | Module | Stacks |
|-------|-----------|--------|--------|
| `def:sheaf-cohomology` | `Scheme.cohomology` | `Cohomology/Basic` | 01FR |
| `def:higher-direct-image` | `Scheme.higherDirectImage` | `Cohomology/Basic` | 01F1 |
| `lem:pf-left-exact` | `Scheme.Modules.pushforward_leftExact` | `Cohomology/Basic` | 01F1 |
| `lem:les` | `Scheme.higherDirectImage_deltaFunctor` | `Cohomology/Basic` | 0156 |
| `lem:hdi-sheafification` | `Scheme.higherDirectImage_isSheafification` | `Cohomology/Basic` | 01E0 |
| `def:flasque` | `TopCat.Presheaf.IsFlasque` | `Cohomology/Flasque` | 01AF |
| `lem:injective-flasque` | `Scheme.Modules.injective_isFlasque` | `Cohomology/Flasque` | 01EA |
| `lem:pushforward-flasque` | `TopCat.Presheaf.isFlasque_pushforward` | `Cohomology/Flasque` | 01E9 |
| `lem:flasque-acyclic` | `Scheme.higherDirectImage_flasque_eq_zero` | `Cohomology/Flasque` | 01EB |
| `lem:acyclic-resolution` | `Scheme.cohomology_of_acyclicResolution` | `Cohomology/Flasque` | 0156 |
| `lem:acyclic-pushforward` | `Scheme.higherDirectImage_pushforward_of_acyclic` | `Cohomology/Flasque` | (Note) |
| `prop:bridge-rderived` | `Scheme.Modules.rightDerivedPushforward_iso_higherDirectImage` | `Cohomology/Bridge` | — |

## WP3 — Čech + vanishing (Part `cech`)

| Label | Lean name | Module | Stacks |
|-------|-----------|--------|--------|
| `def:cech` | `Scheme.cechComplex`, `Scheme.cechCohomology` | `Cech/Complex` | 01ED |
| `lem:cech-basic` | `Scheme.cechCohomology_zero` | `Cech/Complex` | 01EF |
| `prop:cech-to-derived` | `Scheme.cechToDerived`, `_iso_of_acyclicCover` | `Cech/Complex` | 01EW |
| `thm:affine-vanishing` | `AlgebraicGeometry.cohomology_qcoh_affine_eq_zero` | `Cech/AffineVanishing` | 01XB |
| `cor:affine-cover-computes` | `Scheme.cechCohomology_iso_cohomology_of_separated` | `Cech/AffineVanishing` | 01X9 |
| `prop:hdi-qcoh` | `Scheme.higherDirectImage_isQuasicoherent` | `Cech/HigherDirectImageQCoh` | 01XJ |
| `prop:hdi-affine-base` | `Scheme.higherDirectImage_over_affine` | `Cech/HigherDirectImageQCoh` | 01XK |

## WP4 — Projective space & Proj (Part `proj`)

| Label | Lean name | Module | Stacks |
|-------|-----------|--------|--------|
| `con:proj-tilde` | `Proj.tildeGraded`, `Proj.twistingSheaf` | `Projective/Twist` | 01M3 |
| `lem:proj-sections` | `Proj.twistingSheaf_restrict` | `Projective/Twist` | 01M3 |
| `prop:proj-graded` | `Proj.coherent_from_gradedModule` | `Projective/Twist` | 01YS |
| `thm:cohomology-Pn` | `cohomology_projectiveSpace_twist` | `Projective/CohomologyProjectiveSpace` | 01XS |
| `cor:Pn-finite-vanish` | `cohomology_projectiveSpace_finite_and_vanishing` | `Projective/CohomologyProjectiveSpace` | 01XS |
| `lem:affine-finite-proj` | `Proj.cohomology_coherent_finite_and_vanishing` | `Projective/SerreProj` | 01YW |

## WP5 — Coherent sheaves (Part `coherent`)

| Label | Lean name | Module | Stacks |
|-------|-----------|--------|--------|
| `def:coherent` | `Scheme.Modules.IsCoherent` | `Coherent/Basic` | 01BU |
| `lem:X-noeth` | `AlgebraicGeometry.locallyNoetherian_of_finiteType` | `Coherent/Basic` | 01T6 |
| `lem:coherent-noeth` | `Scheme.Modules.isCoherent_iff_qcoh_finiteType` | `Coherent/Basic` | 01XZ |
| `lem:fp-iff-coh` | `Scheme.Modules.isFinitePresentation_iff_isCoherent` | `Coherent/Basic` | 01XZ |
| `prop:coherent-abelian` | `Scheme.Modules.isCoherent_of_ses` | `Coherent/Basic` | 01Y0 |
| `lem:closed-immersion-acyclic` | `Scheme.closedImmersion_pushforward_coherent_and_acyclic` | `Coherent/ClosedSupport` | 01Y6 |
| `lem:support` | `Scheme.Modules.support_closed`, `genericStalk_finrank` | `Coherent/ClosedSupport` | 01YB |

## WP6 — Projective morphisms (Part `projmor`)

| Label | Lean name | Module | Stacks |
|-------|-----------|--------|--------|
| `def:projective-morphism` | `Scheme.IsRelativelyAmple`, `AlgebraicGeometry.IsProjective` | `ProjectiveMorphism/Ample` | 01VG |
| `lem:pullback-ample` | `Scheme.relativelyAmple_pullback_twist` | `ProjectiveMorphism/Ample` | 02NR |
| `lem:graded-finiteness` | `Scheme.gradedCohomology_finite_projective` | `ProjectiveMorphism/HigherDirectImage` | 02O0 |
| `lem:proj-hdi-vanish` | `Scheme.higherDirectImage_vanishing_relativelyAmple` | `ProjectiveMorphism/HigherDirectImage` | 02O1 |
| `lem:proj-hdi-coherent` | `Scheme.higherDirectImage_coherent_of_projective` | `ProjectiveMorphism/HigherDirectImage` | 02O4 |

## WP7 — Dévissage / WP8 — Chow / WP9 — Assembly

| Label | Lean name | Module | Stacks |
|-------|-----------|--------|--------|
| `lem:devissage-gen` | `Scheme.devissage_generation` | `Devissage` | 01YG |
| `thm:devissage` | `Scheme.coherent_devissage` | `Devissage` | 01YI |
| `thm:chow` | `AlgebraicGeometry.chowLemma` | `Chow` | 0200 |
| `rem:chow-graph` | `AlgebraicGeometry.chowLemma_graph_closedImmersion` | `Chow` | 0201 |
| `thm:finiteness` | `Scheme.higherDirectImage_coherent_of_isProper` | `Finiteness` | 02O5 |
| `thm:target-final` | `Scheme.rightDerivedPushforward_isFinitePresentation_of_isProper` | `Target` | 02O5 |

## Companion — Cohomology and base change (Mumford, *Abelian Varieties* p.53)

| Statement | Lean name | Module | Reference |
|-----------|-----------|--------|-----------|
| Thm 0.1 (Buzzard, *Explicit models…*) | `Scheme.higherDirectImage_commutesWithBaseChange_of_fiberVanishing` | `BaseChange` | Mumford §II.5 p.53; Stacks 0A1H |
| relative flatness | `Scheme.Modules.FlatOver` | `BaseChange` | — |
| fibrewise cohomology vanishing | `Scheme.Modules.FiberCohomologyVanishes` | `BaseChange` | — |
| commutes with base change | `Scheme.Modules.CommutesWithBaseChange` | `BaseChange` | — |
