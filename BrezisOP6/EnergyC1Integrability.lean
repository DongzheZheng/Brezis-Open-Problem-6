import BrezisOP6.EnergySmoothBallBridge

/-!
# Finite energy of a concrete `C¹` Euclidean field

The spatial energy in the single-profile identity is an ordinary
finite-dimensional Fréchet-gradient energy.  Continuity of a field and
of its Fréchet derivative on the closed ball makes its density integrable
there, and hence on both the open and punctured balls.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- The coordinate-gradient square is continuous on a set on which the
actual Fréchet derivative is continuous. -/
theorem euclideanGradientSq_continuousOn_of_fderiv
    (n : ℕ) (u : GLEuclidean n → GLEuclidean n)
    (s : Set (GLEuclidean n))
    (hdu : ContinuousOn (fderiv ℝ u) s) :
    ContinuousOn (euclideanGradientSq n u) s := by
  unfold euclideanGradientSq
  fun_prop

/-- A concrete `C¹` field has finite Ginzburg--Landau energy on a closed
Euclidean ball.  The continuity hypotheses are precisely the two pieces
of `C¹` needed here. -/
theorem euclideanGLDensity_integrableOn_closedBall_of_C1
    (n : ℕ) (R : ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hu : ContinuousOn u (Metric.closedBall (0 : GLEuclidean n) R))
    (hdu : ContinuousOn (fderiv ℝ u)
      (Metric.closedBall (0 : GLEuclidean n) R)) :
    IntegrableOn (euclideanGLDensity n u)
      (Metric.closedBall (0 : GLEuclidean n) R) volume := by
  have hgrad := euclideanGradientSq_continuousOn_of_fderiv n u _ hdu
  have hdensity : ContinuousOn (euclideanGLDensity n u)
      (Metric.closedBall (0 : GLEuclidean n) R) := by
    unfold euclideanGLDensity
    fun_prop
  exact hdensity.integrableOn_compact (isCompact_closedBall _ _)

/-- The same `C¹` hypotheses imply the concrete energy integrability
assumption used by the punctured-ball identity. -/
theorem euclideanGLDensity_integrableOn_positiveBall_of_C1
    (m : ℕ) (R : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hdu : ContinuousOn (fderiv ℝ u)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R)) :
    IntegrableOn (euclideanGLDensity (m + 3) u)
      (energyPositiveClosedBall (m + 3) R) volume := by
  apply (euclideanGLDensity_integrableOn_closedBall_of_C1
    (m + 3) R u hu hdu).mono_set
  intro x hx
  simpa [Metric.mem_closedBall, dist_zero_right] using hx.2

/-- A concrete `C¹` numerator has uniform value and squared-gradient
bounds on every compact closed ball.  These are the bounds used in the
inverse-square quotient estimate near the origin. -/
theorem euclideanC1_closedBall_bounds (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean n) R))
    (hdu : ContinuousOn (fderiv ℝ u)
      (Metric.closedBall (0 : GLEuclidean n) R)) :
    ∃ Cu Cg : ℝ, 0 ≤ Cu ∧ 0 ≤ Cg ∧
      ∀ x ∈ Metric.closedBall (0 : GLEuclidean n) R,
        ‖u x‖ ≤ Cu ∧ euclideanGradientSq n u x ≤ Cg := by
  have hcompact : IsCompact
      (Metric.closedBall (0 : GLEuclidean n) R) :=
    isCompact_closedBall _ _
  obtain ⟨Cu, hCu⟩ := hcompact.exists_bound_of_continuousOn hu
  have hgrad := euclideanGradientSq_continuousOn_of_fderiv n u _ hdu
  obtain ⟨Cg, hCg⟩ := hcompact.exists_bound_of_continuousOn hgrad
  refine ⟨max Cu 0, max Cg 0, le_max_right _ _,
    le_max_right _ _, ?_⟩
  intro x hx
  constructor
  · exact (hCu x hx).trans (le_max_left _ _)
  · have habs := hCg x hx
    have hle : euclideanGradientSq n u x ≤
        ‖euclideanGradientSq n u x‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (euclideanGradientSq n u x))
    exact (hle.trans habs).trans (le_max_left _ _)

end

end BrezisOP6
