import BrezisOP6.EnergyConcreteReducedDensity
import BrezisOP6.EnergyActualFieldsIntegrable

/-!
# Transferring reduced-density integrability between representatives

The shared two-profile quotient is represented by different smooth
numerators in the two single-profile identities.  On the punctured ball
these quotient representatives agree, so their actual Fréchet
derivatives agree locally.  The origin and outer sphere are null sets.
-/

namespace BrezisOP6

open MeasureTheory Metric Filter
open scoped Topology

noncomputable section

/-- Equality of two quotient fields on the punctured open ball transfers
integrability of the actual reduced density for every radial profile. -/
theorem energyReducedSpatialDensity_integrableOn_of_eq_off_origin_on_ball
    (m : ℕ) (R : ℝ) (p : ℝ → ℝ)
    (z z' : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (h : ∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 → z x = z' x)
    (hInt : IntegrableOn (energyReducedSpatialDensity m p z')
      (energyPositiveClosedBall (m + 3) R) volume) :
    IntegrableOn (energyReducedSpatialDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume := by
  letI : NeZero (m + 3) := ⟨by omega⟩
  have hne : ∀ᵐ x : GLEuclidean (m + 3)
      ∂(volume : Measure (GLEuclidean (m + 3))), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hEq : (energyReducedSpatialDensity m p z) =ᵐ[
      volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)]
      (energyReducedSpatialDensity m p z') := by
    filter_upwards [ae_restrict_of_ae hne,
      ae_restrict_mem measurableSet_ball] with x hx0 hxBall
    have hnear : z =ᶠ[𝓝 x] z' := by
      filter_upwards [(isOpen_ball).mem_nhds hxBall,
        eventually_ne_nhds hx0] with y hyBall hy0
      exact h y hyBall hy0
    have hgrad : euclideanGradientSq (m + 3) z x =
        euclideanGradientSq (m + 3) z' x := by
      unfold euclideanGradientSq
      rw [hnear.fderiv_eq]
    simp only [energyReducedSpatialDensity, h x hxBall hx0, hgrad]
  have hBall : Integrable (energyReducedSpatialDensity m p z')
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) := by
    change Integrable (energyReducedSpatialDensity m p z')
      (volume.restrict (energyPositiveClosedBall (m + 3) R)) at hInt
    rw [energyPositiveClosedBall_restrict_eq_ball m R] at hInt
    exact hInt
  have hBall' := hBall.congr hEq.symm
  change Integrable (energyReducedSpatialDensity m p z)
    (volume.restrict (energyPositiveClosedBall (m + 3) R))
  rw [energyPositiveClosedBall_restrict_eq_ball m R]
  exact hBall'

/-- Apply the preceding transfer to the second profile of the actual
two-profile bridge.  The smooth transformed numerator `v=F(u/f)`
represents the same shared quotient away from the origin. -/
theorem energyReducedSpatialDensity_shared_quotient_integrable_of_transformed
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hFpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < F r)
    (hInt : IntegrableOn
      (energyReducedSpatialDensity m F
        (fun x : GLEuclidean (m + 3) =>
          (F ‖x‖)⁻¹ •
            energyQuotientNumerator (m + 3) f F α β u x))
      (energyPositiveClosedBall (m + 3) R) volume) :
    IntegrableOn
      (energyReducedSpatialDensity m F
        (fun x : GLEuclidean (m + 3) =>
          (f ‖x‖)⁻¹ • u x))
      (energyPositiveClosedBall (m + 3) R) volume := by
  apply energyReducedSpatialDensity_integrableOn_of_eq_off_origin_on_ball
    m R F
    (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
    (fun x : GLEuclidean (m + 3) =>
      (F ‖x‖)⁻¹ • energyQuotientNumerator (m + 3) f F α β u x)
    ?_ hInt
  intro x hx hx0
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hrle : ‖x‖ ≤ R := by
    have hrlt : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact le_of_lt hrlt
  have hFne : F ‖x‖ ≠ 0 := ne_of_gt (hFpos ‖x‖ hrpos hrle)
  change (f ‖x‖)⁻¹ • u x =
    (F ‖x‖)⁻¹ • energyQuotientNumerator (m + 3) f F α β u x
  rw [energyQuotientNumerator_eq_profile_quotient_off_origin
    (m + 3) f F α β u x hx0, smul_smul,
    inv_mul_cancel₀ hFne, one_smul]

end

end BrezisOP6
