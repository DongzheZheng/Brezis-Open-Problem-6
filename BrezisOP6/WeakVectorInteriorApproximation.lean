import BrezisOP6.WeakSmoothVectorCoordinates
import BrezisOP6.WeakFiniteCoordinateLp

/-!
# One actual vector-valued interior sequence

The diagonalized scalar mollifiers are reassembled without changing their
common scale or mollification index. Their value and gradient coordinates
converge to those of the original zero-extended Sobolev difference.
-/

namespace BrezisOP6

open MeasureTheory Filter Metric
open scoped Topology ENNReal

noncomputable section

/-- A certified global weak gradient is genuinely square-integrable in
each Euclidean input direction, as a vector-valued field. -/
theorem HasGlobalWeakGradient.gradient_direction_memLp_two
    {n : ℕ} {u : GLEuclidean n → GLEuclidean n}
    {G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n}
    (h : HasGlobalWeakGradient n u G) (i : Fin n) :
    MemLp (fun x => G x (EuclideanSpace.single i (1 : ℝ))) 2 volume := by
  let ei : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
  let ev : (GLEuclidean n →L[ℝ] GLEuclidean n) →L[ℝ] GLEuclidean n :=
    ContinuousLinearMap.apply ℝ (GLEuclidean n) ei
  have hMeas : AEStronglyMeasurable (fun x => G x ei) volume :=
    ev.continuous.aestronglyMeasurable.comp_aemeasurable h.2.1.aemeasurable
  have hSq : Integrable (fun x => ‖G x ei‖ ^ 2) volume := by
    apply Integrable.mono_nonneg h.2.2.2.2.1 (hMeas.norm.pow 2)
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · exact Filter.Eventually.of_forall fun x => by
        change ‖G x ei‖ ^ 2 ≤ ∑ k : Fin n,
          ‖G x (EuclideanSpace.single k (1 : ℝ))‖ ^ 2
        exact Finset.single_le_sum
          (f := fun k : Fin n =>
            ‖G x (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
          (fun k hk => sq_nonneg _) (Finset.mem_univ i)
  simpa only [ei] using (memLp_two_iff_integrable_sq_norm hMeas).2 hSq

theorem WeakFixedTraceCompetitor.exists_coordinate_vector_approx_of_zeroTrace
    {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) :
    ∃ q : ℕ → GLEuclidean n → GLEuclidean n,
      (∀ k, ContDiff ℝ 1 (q k)) ∧
      (∀ k x, R ≤ ‖x‖ → q k x = 0) ∧
      (∀ j : Fin n, Tendsto (fun k => eLpNorm
        (fun x => (q k x -
          zeroExtendedDifference n R U.field.u base.u x) j)
        4 volume) atTop (nhds 0)) ∧
      (∀ j i : Fin n, Tendsto (fun k => lpNorm
        (fun x => ((fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            zeroExtendedGradientDifference n R U.field.grad base.grad
              x (EuclideanSpace.single i (1 : ℝ))) j)
        2 volume) atTop (nhds 0)) := by
  obtain ⟨φ, hSmooth, _hCompact, hSupport, hValue, hGradient⟩ :=
    U.exists_coordinate_joint_approx_of_zeroTrace hR base
  let q (k : ℕ) : GLEuclidean n → GLEuclidean n :=
    coordinateSmoothVector (fun j => φ j k)
  have hQ (k : ℕ) : ContDiff ℝ 1 (q k) :=
    coordinateSmoothVector_contDiff (fun j => φ j k)
      (fun j => (hSmooth j k).of_le (by simp))
  refine ⟨q, hQ, ?_, ?_, ?_⟩
  · intro k x hx
    exact coordinateSmoothVector_zero_outside (fun j => φ j k)
      (fun j => hSupport j k) x hx
  · intro j
    have hfun (k : ℕ) :
        (fun x => (q k x -
          zeroExtendedDifference n R U.field.u base.u x) j) =
        (fun x => φ j k x -
          (zeroExtendedDifference n R U.field.u base.u x) j) := by
      funext x
      simp only [PiLp.sub_apply, q, coordinateSmoothVector_apply]
    simp only [hfun]
    exact hValue j
  · intro j i
    have hfun (k : ℕ) :
        (fun x => ((fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            zeroExtendedGradientDifference n R U.field.grad base.grad
              x (EuclideanSpace.single i (1 : ℝ))) j) =
        (fun x => (fderiv ℝ (φ j k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            (zeroExtendedGradientDifference n R U.field.grad base.grad
              x (EuclideanSpace.single i (1 : ℝ))) j) := by
      funext x
      simp only [PiLp.sub_apply, q]
      exact congrArg (fun t : ℝ => t -
        (zeroExtendedGradientDifference n R U.field.grad base.grad
          x (EuclideanSpace.single i (1 : ℝ))) j)
        (coordinateSmoothVector_fderiv_apply (fun t => φ t k)
          (fun t => (hSmooth t k).of_le (by simp))
          x (EuclideanSpace.single i (1 : ℝ)) j)
    simp only [hfun]
    exact hGradient j i

/-- The same approximating vector fields converge in the actual
vector-valued `L⁴` norm and in each directional vector-valued `L²`
weak-gradient norm.  In particular the finite list of scalar
approximations has not changed the intended Sobolev topology. -/
theorem WeakFixedTraceCompetitor.exists_vector_strong_approx_of_zeroTrace
    {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) :
    ∃ q : ℕ → GLEuclidean n → GLEuclidean n,
      (∀ k, ContDiff ℝ 1 (q k)) ∧
      (∀ k x, R ≤ ‖x‖ → q k x = 0) ∧
      Tendsto (fun k => eLpNorm
        (fun x => q k x -
          zeroExtendedDifference n R U.field.u base.u x)
        4 volume) atTop (nhds 0) ∧
      (∀ i : Fin n, Tendsto (fun k => lpNorm
        (fun x => (fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            zeroExtendedGradientDifference n R U.field.grad base.grad
              x (EuclideanSpace.single i (1 : ℝ)))
        2 volume) atTop (nhds 0)) := by
  obtain ⟨q, hC1, hZero, hValue, hGradient⟩ :=
    U.exists_coordinate_vector_approx_of_zeroTrace hR base
  let w := zeroExtendedDifference n R U.field.u base.u
  let G := zeroExtendedGradientDifference n R U.field.grad base.grad
  have hValMeas (k : ℕ) : AEStronglyMeasurable
      (fun x => q k x - w x) volume :=
    (hC1 k).continuous.aestronglyMeasurable.sub U.zeroTrace.1
  have hCoordMeas (k : ℕ) (j : Fin n) : AEStronglyMeasurable
      (fun x => (q k x - w x) j) volume :=
    (EuclideanSpace.proj j).continuous.aestronglyMeasurable.comp_aemeasurable
      (hValMeas k).aemeasurable
  have hValBound (k : ℕ) : eLpNorm
      (fun x => q k x - w x) 4 volume ≤
      ∑ j : Fin n, eLpNorm (fun x => (q k x - w x) j) 4 volume :=
    eLpNorm_euclidean_le_sum_coordinates n _ 4 (by norm_num) (hCoordMeas k)
  have hValSum : Tendsto
      (fun k => ∑ j : Fin n,
        eLpNorm (fun x => (q k x - w x) j) 4 volume)
      atTop (nhds 0) := by
    have h := tendsto_finset_sum Finset.univ (fun j _ => hValue j)
    simpa only [Finset.sum_const_zero] using h
  have hValLimit : Tendsto (fun k => eLpNorm
      (fun x => q k x - w x) 4 volume) atTop (nhds 0) := by
    refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ζ hζ
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hValSum ζ hζ] with k hk
    exact (hValBound k).trans hk
  have hCompact (k : ℕ) : HasCompactSupport (q k) := by
    apply HasCompactSupport.intro'
      (K := Metric.closedBall (0 : GLEuclidean n) R)
      (isCompact_closedBall (0 : GLEuclidean n) R) isClosed_closedBall
    intro x hx
    have hnot : ¬ ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact hZero k x (lt_of_not_ge hnot).le
  have hGradCoordMem (k : ℕ) (j i : Fin n) : MemLp
      (fun x => ((fderiv ℝ (q k) x)
        (EuclideanSpace.single i (1 : ℝ)) -
          G x (EuclideanSpace.single i (1 : ℝ))) j)
      2 volume := by
    let ei : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
    have hDerivCont : Continuous (fun x => (fderiv ℝ (q k) x) ei) :=
      ((hC1 k).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hDerivVec : MemLp (fun x => (fderiv ℝ (q k) x) ei)
        2 volume := hDerivCont.memLp_of_hasCompactSupport
          ((hCompact k).fderiv_apply (𝕜 := ℝ) ei)
    have hDerivCoordMeas : AEStronglyMeasurable
        (fun x => ((fderiv ℝ (q k) x) ei) j) volume :=
      (EuclideanSpace.proj j).continuous.aestronglyMeasurable.comp_aemeasurable
        hDerivVec.aestronglyMeasurable.aemeasurable
    have hDerivCoord : MemLp
        (fun x => ((fderiv ℝ (q k) x) ei) j) 2 volume :=
      hDerivVec.of_le hDerivCoordMeas
        (Filter.Eventually.of_forall fun x =>
          PiLp.norm_apply_le ((fderiv ℝ (q k) x) ei) j)
    simpa only [PiLp.sub_apply, ei] using
      hDerivCoord.sub (U.zeroTrace.gradient_component_memLp_two j i)
  have hGradLimit (i : Fin n) : Tendsto (fun k => lpNorm
      (fun x => (fderiv ℝ (q k) x)
        (EuclideanSpace.single i (1 : ℝ)) -
          G x (EuclideanSpace.single i (1 : ℝ)))
      2 volume) atTop (nhds 0) := by
    have hBound (k : ℕ) : lpNorm
        (fun x => (fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            G x (EuclideanSpace.single i (1 : ℝ)))
        2 volume ≤
      ∑ j : Fin n, lpNorm
        (fun x => ((fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            G x (EuclideanSpace.single i (1 : ℝ))) j)
        2 volume :=
      lpNorm_euclidean_le_sum_coordinates n _ 2 (by norm_num)
        (fun j => hGradCoordMem k j i)
    have hSum : Tendsto (fun k => ∑ j : Fin n, lpNorm
        (fun x => ((fderiv ℝ (q k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            G x (EuclideanSpace.single i (1 : ℝ))) j)
        2 volume) atTop (nhds 0) := by
      have h := tendsto_finset_sum Finset.univ (fun j _ => hGradient j i)
      simpa only [Finset.sum_const_zero] using h
    apply squeeze_zero
    · intro k
      exact lpNorm_nonneg
    · exact hBound
    · exact hSum
  refine ⟨q, hC1, hZero, ?_, ?_⟩
  · simpa only [w] using hValLimit
  · intro i
    simpa only [G] using hGradLimit i

/-- The derivative error of any compactly supported `C¹` perturbation is
an honest global `L²` field.  This rules out totalized `lpNorm` behavior
when the whole-space estimate is restricted to the physical ball. -/
theorem WeakFixedTraceCompetitor.compact_perturbation_gradient_error_memLp
    {n : ℕ} [NeZero n] {R : ℝ}
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base)
    (q : GLEuclidean n → GLEuclidean n)
    (hqC1 : ContDiff ℝ 1 q)
    (hqCompact : HasCompactSupport q)
    (i : Fin n) :
    MemLp (fun x => (fderiv ℝ q x)
      (EuclideanSpace.single i (1 : ℝ)) -
        zeroExtendedGradientDifference n R U.field.grad base.grad
          x (EuclideanSpace.single i (1 : ℝ))) 2 volume := by
  let ei : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
  have hDcont : Continuous (fun x => (fderiv ℝ q x) ei) :=
    (hqC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hD : MemLp (fun x => (fderiv ℝ q x) ei) 2 volume :=
    hDcont.memLp_of_hasCompactSupport
      (hqCompact.fderiv_apply (𝕜 := ℝ) ei)
  simpa only [ei] using
    hD.sub (U.zeroTrace.gradient_direction_memLp_two i)

end

end BrezisOP6
