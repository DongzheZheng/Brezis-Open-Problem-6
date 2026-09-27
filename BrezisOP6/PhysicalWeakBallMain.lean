import BrezisOP6.ActualSmoothAnnularEnergyGap
import BrezisOP6.WeakAnnularEqualityLimit
import BrezisOP6.WeakFixedTraceDensity
import BrezisOP6.WeakAnnulusMeasure

/-!
# The weak fixed-trace ball theorem

The density sequence is constructed from the zero-extended weak
difference.  Uniform smooth annular stability passes through strong
`H¹ ∩ L⁴` convergence.  Thus no equality-case regularity premise is
needed for the weak minimizer.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

theorem physical_weak_ball_minimum_and_ae_equality
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor
      (WeakH1L4BallField.ofGlobalC1 (m + 3) R
        (radialRegularField (m + 3) p.Hf)
        (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf))) :
    let base := WeakH1L4BallField.ofGlobalC1 (m + 3) R
      (radialRegularField (m + 3) p.Hf)
      (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf)
    base.energy ≤ U.field.energy ∧
      (U.field.energy = base.energy →
        U.field.u =ᵐ[weakBallMeasure (m + 3) R] base.u) := by
  let base : WeakH1L4BallField (m + 3) R :=
    WeakH1L4BallField.ofGlobalC1 (m + 3) R
      (radialRegularField (m + 3) p.Hf)
      (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf)
  have hBaseEnergy : base.energy =
      euclideanBallEnergy (m + 3) R
        (radialVortex (m + 3) p.f) := by
    exact radialRegularField_weak_energy_eq_vortex
      (m + 3) R p.f p.Hf p.hHf p.hfFactor
  have hClosure : WeakSmoothFixedTraceStrongClosure m R p.f U.field :=
    physical_weak_fixed_trace_strong_closure m R p U
  have hStable : ∀ δ ρ : ℝ, 0 < δ → δ < ρ → ρ < R →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ V : WeakH1L4BallField (m + 3) R,
          SmoothBallCompetitor m R p.f V.u →
          V.grad = fderiv ℝ V.u →
          (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
              ‖V.u x - base.u x‖ ^ 2
                ∂(weakBallMeasure (m + 3) R)) ≤
            C * (V.energy - base.energy) := by
    intro δ ρ hδ hδρ hρR
    obtain ⟨C, hC, hSmooth⟩ :=
      actual_smooth_annular_energy_gap_uniform
        m R p hPublished hLocal δ ρ hδ hδρ.le hρR
    refine ⟨C, hC.le, ?_⟩
    intro V hVSmooth hVGrad
    let s := energyPositiveAnnulus (m + 3) δ ρ
    have hSubset : s ⊆ Metric.ball
        (0 : GLEuclidean (m + 3)) R := by
      intro x hx
      change ‖x‖ ∈ Ioc δ ρ at hx
      simpa only [Metric.mem_ball, dist_zero_right] using
        (lt_of_le_of_lt hx.2 hρR)
    have hBasePoint : ∀ x ∈ s,
        base.u x = radialVortex (m + 3) p.f x := by
      intro x hx
      exact radialRegularField_eq_vortex_on_ball
        (m + 3) R p.f p.Hf p.hfFactor x (hSubset hx)
    have hIntegral :
        (∫ x in s, ‖V.u x - base.u x‖ ^ 2
          ∂(weakBallMeasure (m + 3) R)) =
        (∫ x in s, ‖V.u x - radialVortex (m + 3) p.f x‖ ^ 2
          ∂volume) := by
      change (∫ x, ‖V.u x - base.u x‖ ^ 2
          ∂((weakBallMeasure (m + 3) R).restrict s)) =
        (∫ x, ‖V.u x - radialVortex (m + 3) p.f x‖ ^ 2
          ∂(volume.restrict s))
      rw [weakBallMeasure_restrict_annulus_eq_volume
        (m + 3) R δ ρ hρR]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_energyPositiveAnnulus (m + 3) δ ρ)] with x hx
      rw [hBasePoint x hx]
    have hVEnergy : V.energy =
        euclideanBallEnergy (m + 3) R V.u := by
      rw [WeakH1L4BallField.energy, hVGrad,
        weakBallEnergy_classical_gradient]
    rw [hIntegral, hVEnergy, hBaseEnergy]
    exact hSmooth V.u hVSmooth
  exact weak_minimum_and_ae_equality_of_strong_closure_and_annular_stability
    m R p base hBaseEnergy hPublished hLocal U hClosure hStable

end

end BrezisOP6
