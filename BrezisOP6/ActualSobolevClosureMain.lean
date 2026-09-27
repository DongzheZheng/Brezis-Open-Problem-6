import BrezisOP6.ActualSmoothMainCanonical
import BrezisOP6.SmoothEnergyClosure

/-!
# The finite-ball comparison and an abstract energy-limit consequence

This module packages the physical radial-profile hypotheses shared by every
smooth competitor.  The geometric comparison then supplies a theorem for
each smooth boundary-matching field.  The subsequent theorem is conditional
on `SmoothBallEnergyClosure` and `EqualityCaseSmoothRepresentative` for the
totalized pointwise-derivative energy.  It does not state the manuscript's
unconditional `H¹ ∩ L⁴` theorem: a weak-gradient formulation, fixed-trace
density, and equality-case regularity are still separate obligations.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

/-- Profile data common to all competitors in a fixed physical ball.  The
fields describe radial ODE solutions and their regularity; the published
entire-space minimum and sphere spectral input are stated separately at the
comparison theorem. -/
structure PhysicalRadialData (m : ℕ) (R : ℝ) where
  f : ℝ → ℝ
  F : ℝ → ℝ
  y : ℝ → ℝ
  Hf : ℝ → ℝ
  HF : ℝ → ℝ
  α : ℝ
  β : ℝ
  Af : ℝ
  Bf : ℝ
  AF : ℝ
  BF : ℝ
  hR : 0 < R
  hα : 0 < α
  hβ : 0 < β
  hfTaylor : RadialOriginTaylorInterior f β Af Bf R
  hFTaylor : RadialOriginTaylorInterior F α AF BF R
  hf0 : f 0 = 0
  hF0 : F 0 = 0
  hHf0 : Hf 0 = β
  hHF0 : HF 0 = α
  hfC2 : ContDiff ℝ 2 f
  hFC2 : ContDiff ℝ 2 F
  hHf : ContDiff ℝ 1 Hf
  hHF : ContDiff ℝ 1 HF
  hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r
  hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1
  hfR : f R = 1
  hyFlt : ∀ r ∈ Ioc (0 : ℝ) R, profileY F r < 1
  hFone : Tendsto F atTop (𝓝 (1 : ℝ))
  hyDiff : Differentiable ℝ y
  hyMatch : ∀ r, 0 < r → y r = profileY F r
  hFposAll : ∀ r, 0 < r → 0 < F r
  hFltAll : ∀ r, 0 < r → F r < 1
  hFodeAll : ∀ r, 0 < r →
    radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
      (deriv (deriv F) r)
  hfODE : ∀ r, 0 < r → r < R →
    radialODEAt ((m : ℝ) + 3) r
      (f r) (deriv f r) (deriv (deriv f) r)
  hfFactor : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2)
  hFFactor : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2)

/-- The canonical smooth comparison, uniformly in the smooth competitor. -/
theorem physical_smooth_ball_minimum_and_ae_equality
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hv : SmoothBallCompetitor m R p.f v) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) p.f) ≤
      euclideanBallEnergy (m + 3) R v ∧
    (euclideanBallEnergy (m + 3) R v =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) p.f) →
        v =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)]
          radialVortex (m + 3) p.f) := by
  exact actual_smooth_ball_minimum_and_ae_equality_canonical
    m R p.hR p.f p.F p.y p.Hf p.HF v
    p.α p.β p.Af p.Bf p.AF p.BF
    p.hα p.hβ p.hfTaylor p.hFTaylor p.hf0 p.hF0
    p.hHf0 p.hHF0 p.hfC2 p.hFC2
    p.hHf p.hHF hv.1 p.hfpos p.hflt p.hfR
    p.hyFlt p.hFone
    p.hyDiff p.hyMatch p.hFposAll p.hFltAll
    p.hFodeAll p.hfODE p.hfFactor p.hFFactor hv.2
    hPublished hLocal

/-- A conditional finite-ball minimum and equality-case uniqueness for
the pointwise-derivative energy under explicit energy-limit and smooth-
representative hypotheses.  These hypotheses are not supplied by Sobolev
membership in this formalization. -/
theorem physical_ball_minimum_and_ae_uniqueness_of_smooth_closure
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hClosure : SmoothBallEnergyClosure m R p.f u)
    (hRegularity : EqualityCaseSmoothRepresentative m R p.f u) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) p.f) ≤
      euclideanBallEnergy (m + 3) R u ∧
    (euclideanBallEnergy (m + 3) R u =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) p.f) →
        u =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)]
          radialVortex (m + 3) p.f) := by
  apply ball_minimum_and_ae_uniqueness_of_smooth_closure
    m R p.f u
  · intro v hv
    exact (physical_smooth_ball_minimum_and_ae_equality
      m R p hPublished hLocal v hv).1
  · intro v hv heq
    exact (physical_smooth_ball_minimum_and_ae_equality
      m R p hPublished hLocal v hv).2 heq
  · exact hClosure
  · exact hRegularity

end

end BrezisOP6
