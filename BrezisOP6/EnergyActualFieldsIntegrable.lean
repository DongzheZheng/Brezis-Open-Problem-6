import BrezisOP6.EnergyRegularBallBridge
import BrezisOP6.EnergyC1Integrability

/-!
# Concrete finite energy of the two fields in the radial identity

The source competitor is smooth on the closed ball.  The radial vortex is
represented there by the smooth map `x ↦ H(‖x‖²)x`.  The totalized quotient
may have an artificial value at the origin, but its profile product has
the same energy density as the smooth competitor almost everywhere.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric
open scoped Topology

noncomputable section

/-- Local agreement away from the origin transfers integrability of the
actual Fréchet-gradient Ginzburg--Landau density on a ball. -/
theorem euclideanGLDensity_integrableOn_of_eq_off_origin_on_ball
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (u v : GLEuclidean n → GLEuclidean n)
    (h : ∀ x ∈ Metric.ball (0 : GLEuclidean n) R,
      x ≠ 0 → u x = v x)
    (hvInt : IntegrableOn (euclideanGLDensity n v)
      (Metric.ball (0 : GLEuclidean n) R) volume) :
    IntegrableOn (euclideanGLDensity n u)
      (Metric.ball (0 : GLEuclidean n) R) volume := by
  letI : NeZero n := ⟨by omega⟩
  have hne : ∀ᵐ x : GLEuclidean n
      ∂(volume : Measure (GLEuclidean n)), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hEq : (euclideanGLDensity n u) =ᵐ[
      volume.restrict (Metric.ball (0 : GLEuclidean n) R)]
      (euclideanGLDensity n v) := by
    filter_upwards [ae_restrict_of_ae hne,
      ae_restrict_mem measurableSet_ball] with x hx0 hxBall
    have hnear : u =ᶠ[𝓝 x] v := by
      filter_upwards [(isOpen_ball).mem_nhds hxBall,
        eventually_ne_nhds hx0] with y hyBall hy0
      exact h y hyBall hy0
    have hderiv : fderiv ℝ u x = fderiv ℝ v x := hnear.fderiv_eq
    unfold euclideanGLDensity
    rw [h x hxBall hx0]
    simp only [euclideanGradientSq]
    rw [hderiv]
  exact hvInt.congr hEq.symm

/-- The profile product of the totalized quotient has finite energy on
the punctured closed ball directly from `C¹` regularity of the original
competitor and profile positivity. -/
theorem quotient_product_GL_integrableOn_positiveBall_of_C1
    (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hdu : ContinuousOn (fderiv ℝ u)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r) :
    IntegrableOn
      (euclideanGLDensity (m + 3)
        (fun y => f ‖y‖ • ((f ‖y‖)⁻¹ • u y)))
      (energyPositiveClosedBall (m + 3) R) volume := by
  have huClosed := euclideanGLDensity_integrableOn_closedBall_of_C1
    (m + 3) R u hu hdu
  have huBall : IntegrableOn (euclideanGLDensity (m + 3) u)
      (Metric.ball (0 : GLEuclidean (m + 3)) R) volume := by
    apply huClosed.mono_set
    intro x hx
    have hr : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt hr
  have hprod : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 →
      f ‖x‖ • ((f ‖x‖)⁻¹ • u x) = u x :=
    energyQuotient_product_eq_on_ball_of_profile_pos
      (m + 3) R f u hfpos
  have hBall := euclideanGLDensity_integrableOn_of_eq_off_origin_on_ball
    (m + 3) (by omega) R
    (fun y => f ‖y‖ • ((f ‖y‖)⁻¹ • u y)) u hprod huBall
  change Integrable _
    (volume.restrict (energyPositiveClosedBall (m + 3) R))
  rw [energyPositiveClosedBall_restrict_eq_ball m R]
  exact hBall

/-- On a finite ball the radial vortex agrees away from the origin with
the globally `C¹` map `x ↦ H(‖x‖²)x`. -/
theorem radialVortex_eq_regular_factor_on_ball
    (n : ℕ) (R : ℝ) (p H : ℝ → ℝ)
    (hp : ∀ r : ℝ, 0 < r → r ≤ R →
      p r = r * H (r ^ 2)) :
    ∀ x ∈ Metric.ball (0 : GLEuclidean n) R,
      x ≠ 0 →
      radialVortex n p x = H (‖x‖ ^ 2) • x := by
  intro x hxBall hx0
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hrle : ‖x‖ ≤ R := by
    have hrlt : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxBall
    exact le_of_lt hrlt
  have hrne : ‖x‖ ≠ 0 := ne_of_gt hrpos
  have hratio : p ‖x‖ / ‖x‖ = H (‖x‖ ^ 2) := by
    rw [hp ‖x‖ hrpos hrle]
    field_simp [hrne]
  simpa only [radialVortex, hratio]

/-- The regular radial factor yields finite vortex energy without
assuming an integrable vortex density. -/
theorem radialVortex_GL_integrableOn_positiveBall_of_factor
    (m : ℕ) (R : ℝ) (p H : ℝ → ℝ)
    (hH : ContDiff ℝ 1 H)
    (hp : ∀ r : ℝ, 0 < r → r ≤ R →
      p r = r * H (r ^ 2)) :
    IntegrableOn (euclideanGLDensity (m + 3)
      (radialVortex (m + 3) p))
      (energyPositiveClosedBall (m + 3) R) volume := by
  let v : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => H (‖x‖ ^ 2) • x
  have hsquare : ContDiff ℝ 1
      (fun x : GLEuclidean (m + 3) => ‖x‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hv : ContDiff ℝ 1 v := by
    exact (hH.comp hsquare).smul contDiff_id
  have hvClosed := euclideanGLDensity_integrableOn_closedBall_of_C1
    (m + 3) R v hv.continuous.continuousOn
      (hv.continuous_fderiv (by norm_num)).continuousOn
  have hvBall : IntegrableOn (euclideanGLDensity (m + 3) v)
      (Metric.ball (0 : GLEuclidean (m + 3)) R) volume := by
    apply hvClosed.mono_set
    intro x hx
    have hr : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt hr
  have hBall := euclideanGLDensity_integrableOn_of_eq_off_origin_on_ball
    (m + 3) (by omega) R (radialVortex (m + 3) p) v
      (radialVortex_eq_regular_factor_on_ball (m + 3) R p H hp)
      hvBall
  change Integrable _
    (volume.restrict (energyPositiveClosedBall (m + 3) R))
  rw [energyPositiveClosedBall_restrict_eq_ball m R]
  exact hBall

end

end BrezisOP6
