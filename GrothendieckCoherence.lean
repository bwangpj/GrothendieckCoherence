-- GrothendieckCoherence: a blueprint-driven scaffold for EGA III, Théorème 3.2.1.
-- See `blueprint/src/content.tex` and `docs/BLUEPRINT_MAP.md`.

-- WP1 — Quasi-coherent sheaves
import GrothendieckCoherence.QuasiCoherent.Tilde
import GrothendieckCoherence.QuasiCoherent.Basic
import GrothendieckCoherence.QuasiCoherent.Invertible
-- WP2 — Cohomology core
import GrothendieckCoherence.Cohomology.Basic
import GrothendieckCoherence.Cohomology.Flasque
import GrothendieckCoherence.Cohomology.Bridge
-- WP3 — Čech + affine vanishing
import GrothendieckCoherence.Cech.Complex
import GrothendieckCoherence.Cech.AffineVanishing
import GrothendieckCoherence.Cech.HigherDirectImageQCoh
-- WP4 — Projective space & Proj
import GrothendieckCoherence.Projective.Twist
import GrothendieckCoherence.Projective.CohomologyProjectiveSpace
import GrothendieckCoherence.Projective.SerreProj
-- WP5 — Coherent sheaves
import GrothendieckCoherence.Coherent.Basic
import GrothendieckCoherence.Coherent.ClosedSupport
-- WP6 — Projective morphisms
import GrothendieckCoherence.ProjectiveMorphism.Ample
import GrothendieckCoherence.ProjectiveMorphism.HigherDirectImage
-- WP7 — Dévissage
import GrothendieckCoherence.Devissage
-- WP8 — Chow's lemma
import GrothendieckCoherence.Chow
-- WP9 — Assembly + bridge to the target statement
import GrothendieckCoherence.Finiteness
import GrothendieckCoherence.Target
-- Companion: cohomology and base change (Mumford, Abelian Varieties p.53)
import GrothendieckCoherence.BaseChange
