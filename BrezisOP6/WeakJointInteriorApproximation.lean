import BrezisOP6.WeakToDeGiorgi
import BrezisOP6.WeakGlobalDilationChainRule
import BrezisOP6.WeakTraceDilationSupport

/-!
# Joint interior approximation of a zero-trace difference

The same scalar mollifications approximate each component of an inward
dilation in `L²`, `L⁴`, and the weak-gradient `L²` norm. Their supports stay
strictly inside the original ball. This is one step toward the full
fixed-trace vector-valued density theorem.
-/

namespace BrezisOP6

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

noncomputable section

private theorem tsupport_component_subset {n : ℕ}
    (u : GLEuclidean n → GLEuclidean n) (j : Fin n) :
    tsupport (fun x => (u x) j) ⊆ tsupport u := by
  change closure (Function.support (fun x => (u x) j)) ⊆
    closure (Function.support u)
  apply closure_mono
  intro x hx
  change (u x) j ≠ 0 at hx
  change u x ≠ 0
  intro hzero
  simp [hzero] at hx

/-- Each coordinate of a globally certified Sobolev field admits one
smooth sequence simultaneously convergent in `L²`, `L⁴`, and every
weak-gradient `L²` component, while retaining prescribed interior support. -/
theorem HasGlobalWeakGradient.component_joint_approx_inside
    {n : ℕ} [NeZero n]
    {u : GLEuclidean n → GLEuclidean n}
    {G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n}
    (h : HasGlobalWeakGradient n u G)
    {K Ω : Set (GLEuclidean n)}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hsupport : tsupport u ⊆ K) (j : Fin n) :
    ∃ ψ : ℕ → GLEuclidean n → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)) ∧
      (∀ k, HasCompactSupport (ψ k)) ∧
      (∀ k, tsupport (ψ k) ⊆ Ω) ∧
      Tendsto (fun k => eLpNorm (fun x => ψ k x - (u x) j) 2 volume)
        atTop (nhds 0) ∧
      (∀ i : Fin n,
        Tendsto (fun k => eLpNorm
          (fun x => (fderiv ℝ (ψ k) x)
            (EuclideanSpace.single i (1 : ℝ)) -
              (G x (EuclideanSpace.single i (1 : ℝ))) j)
          2 volume) atTop (nhds 0)) ∧
      Tendsto (fun k => eLpNorm (fun x => ψ k x - (u x) j) 4 volume)
        atTop (nhds 0) := by
  have hcompSupport : tsupport (fun x => (u x) j) ⊆ K :=
    (tsupport_component_subset u j).trans hsupport
  let hw : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (fun x => (u x) j) Set.univ := h.component_W12Witness j
  obtain ⟨ψ, hψsmooth, hψcompact, hψsupport, hψtwo, hψgrad, hψfour⟩ :=
    DeGiorgi.exists_smooth_W1p_L4_approx_inside_open
      (d := n) hΩ (p := 2) (by norm_num) hw (h.component_memLp_four j)
      hK hKΩ hcompSupport
  refine ⟨ψ, hψsmooth, hψcompact, hψsupport, ?_, ?_, hψfour⟩
  · simpa using hψtwo
  · intro i
    have hwgrad (x : GLEuclidean n) :
        hw.weakGrad x i =
          (G x (EuclideanSpace.single i (1 : ℝ))) j := by
      simp [hw, HasGlobalWeakGradient.component_W12Witness]
    simpa [hwgrad] using hψgrad i

/-- The inward dilation of an actual fixed-trace difference has, in every
output coordinate, compactly supported mollifications strictly inside the
original ball with joint `L²`, `L⁴`, and weak-gradient `L²` convergence. -/
theorem WeakFixedTraceCompetitor.inward_component_joint_approx
    {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (j : Fin n) :
    ∃ ψ : ℕ → GLEuclidean n → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)) ∧
      (∀ k, HasCompactSupport (ψ k)) ∧
      (∀ k, tsupport (ψ k) ⊆ Metric.ball (0 : GLEuclidean n) R) ∧
      Tendsto (fun k => eLpNorm
        (fun x => ψ k x -
          (inwardDilation n a
            (zeroExtendedDifference n R U.field.u base.u) x) j)
        2 volume) atTop (nhds 0) ∧
      (∀ i : Fin n,
        Tendsto (fun k => eLpNorm
          (fun x => (fderiv ℝ (ψ k) x)
            (EuclideanSpace.single i (1 : ℝ)) -
              (inwardGradient n a
                (zeroExtendedGradientDifference n R U.field.grad base.grad)
                x (EuclideanSpace.single i (1 : ℝ))) j)
          2 volume) atTop (nhds 0)) ∧
      Tendsto (fun k => eLpNorm
        (fun x => ψ k x -
          (inwardDilation n a
            (zeroExtendedDifference n R U.field.u base.u) x) j)
        4 volume) atTop (nhds 0) := by
  let w := zeroExtendedDifference n R U.field.u base.u
  let H := zeroExtendedGradientDifference n R U.field.grad base.grad
  have hglobal : HasGlobalWeakGradient n
      (inwardDilation n a w) (inwardGradient n a H) := by
    simpa [inwardDilation, inwardGradient, w, H] using
      (HasGlobalWeakGradient.dilate n a⁻¹ (inv_pos.mpr ha) w H U.zeroTrace)
  have hsupp : tsupport (inwardDilation n a w) ⊆
      Metric.closedBall (0 : GLEuclidean n) (a * R) :=
    inward_zeroExtendedDifference_tsupport_subset_closedBall n R a ha
      U.field.u base.u
  have hsub : Metric.closedBall (0 : GLEuclidean n) (a * R) ⊆
      Metric.ball (0 : GLEuclidean n) R := by
    intro x hx
    have hnorm : ‖x‖ ≤ a * R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hstrict : a * R < R := by
      have hgap := mul_pos (sub_pos.mpr ha1) hR
      nlinarith
    simpa [Metric.mem_ball, dist_zero_right] using hnorm.trans_lt hstrict
  exact hglobal.component_joint_approx_inside
    (isCompact_closedBall (0 : GLEuclidean n) (a * R))
    isOpen_ball hsub hsupp j

/-- One common sequence index approximates all finitely many output
coordinates. Each coordinate itself is smoothed by one normalized kernel,
so its `L²`, `L⁴`, and derivative `L²` limits are synchronized. -/
theorem WeakFixedTraceCompetitor.inward_all_components_joint_approx
    {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ ψ : Fin n → ℕ → GLEuclidean n → ℝ,
      (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (ψ j k)) ∧
      (∀ j k, HasCompactSupport (ψ j k)) ∧
      (∀ j k, tsupport (ψ j k) ⊆ Metric.ball (0 : GLEuclidean n) R) ∧
      (∀ j, Tendsto (fun k => eLpNorm
        (fun x => ψ j k x -
          (inwardDilation n a
            (zeroExtendedDifference n R U.field.u base.u) x) j)
        2 volume) atTop (nhds 0)) ∧
      (∀ j i, Tendsto (fun k => eLpNorm
        (fun x => (fderiv ℝ (ψ j k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            (inwardGradient n a
              (zeroExtendedGradientDifference n R U.field.grad base.grad)
              x (EuclideanSpace.single i (1 : ℝ))) j)
        2 volume) atTop (nhds 0)) ∧
      (∀ j, Tendsto (fun k => eLpNorm
        (fun x => ψ j k x -
          (inwardDilation n a
            (zeroExtendedDifference n R U.field.u base.u) x) j)
        4 volume) atTop (nhds 0)) := by
  classical
  have hj (j : Fin n) := U.inward_component_joint_approx hR base a ha ha1 j
  choose ψ hSmooth hCompact hSupport hTwo hGrad hFour using hj
  exact ⟨ψ, hSmooth, hCompact, hSupport, hTwo,
    (fun j i => hGrad j i), hFour⟩

end

end BrezisOP6
