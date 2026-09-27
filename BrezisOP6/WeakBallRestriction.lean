import BrezisOP6.WeakVectorInteriorApproximation

/-!
# Restriction of strong whole-space convergence to the finite ball

These lemmas pass the actual global Sobolev norms of the interior
approximants to the ball measure.  The real-valued norm statement keeps
an explicit `MemLp` certificate to avoid Mathlib's totalized convention.
-/

namespace BrezisOP6

open MeasureTheory Filter Metric
open scoped ENNReal Topology

noncomputable section

theorem eLpNorm_restrict_tendsto_zero_of_global
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (s : Set α) (p : ℝ≥0∞)
    (f : ℕ → α → E)
    (h : Tendsto (fun k => eLpNorm (f k) p μ) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (f k) p (μ.restrict s))
      atTop (nhds 0) := by
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ζ hζ
  filter_upwards [ENNReal.tendsto_nhds_zero.1 h ζ hζ] with k hk
  exact (eLpNorm_restrict_le (f k) p μ s).trans hk

theorem lpNorm_restrict_tendsto_zero_of_global
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (s : Set α) (p : ℝ≥0∞)
    (f : ℕ → α → E) (hf : ∀ k, MemLp (f k) p μ)
    (h : Tendsto (fun k => lpNorm (f k) p μ) atTop (nhds 0)) :
    Tendsto (fun k => lpNorm (f k) p (μ.restrict s))
      atTop (nhds 0) := by
  have hE : Tendsto (fun k => eLpNorm (f k) p μ)
      atTop (nhds 0) := by
    have ht := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h
    have hEq :
        (ENNReal.ofReal ∘ fun k => lpNorm (f k) p μ) =
          (fun k => eLpNorm (f k) p μ) := by
      funext k
      exact ofReal_lpNorm (hf k)
    rw [hEq] at ht
    simpa using ht
  have hER := eLpNorm_restrict_tendsto_zero_of_global s p f hE
  have ht :=
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hER
  have hEq :
      (ENNReal.toReal ∘ fun k => eLpNorm (f k) p (μ.restrict s)) =
        (fun k => lpNorm (f k) p (μ.restrict s)) := by
    funext k
    exact toReal_eLpNorm ((hf k).restrict s).aestronglyMeasurable
  rw [hEq] at ht
  simpa using ht

theorem lpNorm_restrict_tendsto_zero_of_global_eLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (s : Set α) (p : ℝ≥0∞)
    (f : ℕ → α → E)
    (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (h : Tendsto (fun k => eLpNorm (f k) p μ) atTop (nhds 0)) :
    Tendsto (fun k => lpNorm (f k) p (μ.restrict s))
      atTop (nhds 0) := by
  have hER := eLpNorm_restrict_tendsto_zero_of_global s p f h
  have ht :=
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hER
  have hEq :
      (ENNReal.toReal ∘ fun k => eLpNorm (f k) p (μ.restrict s)) =
        (fun k => lpNorm (f k) p (μ.restrict s)) := by
    funext k
    exact toReal_eLpNorm ((hf k).mono_measure Measure.restrict_le_self)
  rw [hEq] at ht
  simpa using ht

/-- The interior vector approximants converge in the exact ball norms
appearing in the paper, including the distributional gradient. -/
theorem WeakFixedTraceCompetitor.exists_ball_strong_approx_of_zeroTrace
    {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) :
    ∃ q : ℕ → GLEuclidean n → GLEuclidean n,
      (∀ k, ContDiff ℝ 1 (q k)) ∧
      (∀ k x, R ≤ ‖x‖ → q k x = 0) ∧
      Tendsto (fun k => lpNorm
        (fun x => q k x -
          zeroExtendedDifference n R U.field.u base.u x)
        4 (weakBallMeasure n R)) atTop (nhds 0) ∧
      (∀ i : Fin n, Tendsto (fun k => lpNorm
        (fun x => (fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            zeroExtendedGradientDifference n R U.field.grad base.grad
              x (EuclideanSpace.single i (1 : ℝ)))
        2 (weakBallMeasure n R)) atTop (nhds 0)) := by
  obtain ⟨q, hC1, hZero, hVal, hGrad⟩ :=
    U.exists_vector_strong_approx_of_zeroTrace hR base
  let w := zeroExtendedDifference n R U.field.u base.u
  let G := zeroExtendedGradientDifference n R U.field.grad base.grad
  have hValMeas (k : ℕ) : AEStronglyMeasurable
      (fun x => q k x - w x) volume :=
    (hC1 k).continuous.aestronglyMeasurable.sub U.zeroTrace.1
  have hValBall : Tendsto
      (fun k => lpNorm (fun x => q k x - w x) 4
        (weakBallMeasure n R)) atTop (nhds 0) := by
    exact lpNorm_restrict_tendsto_zero_of_global_eLp
      (Metric.ball (0 : GLEuclidean n) R) 4
      (fun k x => q k x - w x) hValMeas hVal
  have hCompact (k : ℕ) : HasCompactSupport (q k) := by
    apply HasCompactSupport.intro'
      (K := Metric.closedBall (0 : GLEuclidean n) R)
      (isCompact_closedBall (0 : GLEuclidean n) R) isClosed_closedBall
    intro x hx
    have hnot : ¬ ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact hZero k x (lt_of_not_ge hnot).le
  have hGradBall (i : Fin n) : Tendsto
      (fun k => lpNorm
        (fun x => (fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            G x (EuclideanSpace.single i (1 : ℝ)))
        2 (weakBallMeasure n R)) atTop (nhds 0) := by
    exact lpNorm_restrict_tendsto_zero_of_global
      (Metric.ball (0 : GLEuclidean n) R) 2
      (fun k x => (fderiv ℝ (q k) x)
        (EuclideanSpace.single i (1 : ℝ)) -
          G x (EuclideanSpace.single i (1 : ℝ)))
      (fun k => U.compact_perturbation_gradient_error_memLp
        base (q k) (hC1 k) (hCompact k) i)
      (hGrad i)
  refine ⟨q, hC1, hZero, ?_, ?_⟩
  · simpa only [w] using hValBall
  · intro i
    simpa only [G] using hGradBall i

end

end BrezisOP6
