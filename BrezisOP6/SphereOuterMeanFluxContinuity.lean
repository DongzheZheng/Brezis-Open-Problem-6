import BrezisOP6.SphereFiniteFamilyOuterL2
import BrezisOP6.SphereFiniteMeanDerivativeInterior
import BrezisOP6.BridgePiconeIdentificationRightLimit

/-!
# The actual zero mode and bridge flux at the outer sphere

The interior `L²` radial derivative and the left `L²` boundary trace
give continuity of the regularized mean on every closed positive-radius
annulus.  This is precisely the regularity required for the annular FTC;
no two-sided derivative at the finite-ball boundary is used.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem finiteBallSphereRadialMean_tendsto_outer_left_of_trace
    (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n)
    (htrace : Tendsto
      (fun r => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r)
      (𝓝[<] R)
      (𝓝 (scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) R))) :
    Tendsto
      (vectorSphereRadialMean n
        (finiteBallSphereFamily n R z)
        (fun s i => finiteBallSphereFamily_memLp n R z hz s i) k)
      (𝓝[<] R)
      (𝓝 (vectorSphereRadialMean n
        (finiteBallSphereFamily n R z)
        (fun s i => finiteBallSphereFamily_memLp n R z hz s i) k R)) := by
  have hmeanCont : Continuous (sphereMeanCoefficient n) := by
    unfold sphereMeanCoefficient
    fun_prop
  have hmean := hmeanCont.continuousAt.tendsto.comp htrace
  have hr : Tendsto (fun r : ℝ => r) (𝓝[<] R) (𝓝 R) :=
    nhdsWithin_le_nhds
  simpa only [vectorSphereRadialMean, scalarSphereRadialMean]
    using hr.mul hmean

theorem finiteBallSphereRadialMean_continuousOn_positive_annulus
    (n : ℕ) (R δ : ℝ) (hδ : 0 < δ) (hδR : δ < R)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n)
    (htrace : Tendsto
      (fun r => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r)
      (𝓝[<] R)
      (𝓝 (scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) R))) :
    ContinuousOn
      (vectorSphereRadialMean n
        (finiteBallSphereFamily n R z)
        (fun s i => finiteBallSphereFamily_memLp n R z hz s i) k)
      (Icc δ R) := by
  let b := vectorSphereRadialMean n
    (finiteBallSphereFamily n R z)
    (fun s i => finiteBallSphereFamily_memLp n R z hz s i) k
  have hleft : Tendsto b (𝓝[<] R) (𝓝 (b R)) :=
    finiteBallSphereRadialMean_tendsto_outer_left_of_trace
      n R z hz k htrace
  intro r hr
  by_cases hrR : r = R
  · subst r
    exact (continuousWithinAt_Icc_iff_Iic hδR).2
      (continuousWithinAt_Iio_iff_Iic.mp hleft)
  · have hrpos : 0 < r := lt_of_lt_of_le hδ hr.1
    have hrlt : r < R := lt_of_le_of_ne hr.2 hrR
    exact ((finiteBallSphereRadialMean_hasDerivAt_interior
      n R z hz k r ⟨hrpos, hrlt⟩).continuousAt).continuousWithinAt

/-- A positive annulus has no singular weight denominator. -/
theorem bridgeOriginFlux_continuousOn_positive_annulus
    (m : ℕ) (f F b : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ < R)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hbCont : ContinuousOn b (Icc δ R)) :
    ContinuousOn (bridgeOriginFlux m f F b) (uIcc δ R) := by
  have hfCont : ContinuousOn f (Icc δ R) := hfDiff.continuous.continuousOn
  have hFCont : ContinuousOn F (Icc δ R) := hFDiff.continuous.continuousOn
  have hnum : ContinuousOn (fun r => f r ^ 2 - F r ^ 2) (Icc δ R) :=
    (hfCont.pow 2).sub (hFCont.pow 2)
  have hden : ContinuousOn (fun r : ℝ => r ^ 2) (Icc δ R) :=
    continuousOn_id.pow 2
  have hweight : ContinuousOn (piconeWeightFromProfiles f F) (Icc δ R) := by
    simpa only [piconeWeightFromProfiles] using
      hnum.div hden (fun r hr => pow_ne_zero 2
        (ne_of_gt (lt_of_lt_of_le hδ hr.1)))
  have hflux : ContinuousOn (bridgeOriginFlux m f F b) (Icc δ R) := by
    simpa only [bridgeOriginFlux] using
      ((continuousOn_id.pow (m + 1)).mul hweight).mul (hbCont.pow 2)
  simpa only [uIcc_of_le hδR.le] using hflux

/-- The annular bridge-flux continuity required by the finite-ball
integration-by-parts theorem follows from the actual smooth quotient and
its prescribed outer boundary value. -/
theorem actual_finiteBallSphere_bridgeOriginFlux_continuousOn
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f)
    (hFDiff : Differentiable ℝ F)
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (k : Fin (m + 3)) (δ : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
    let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
      fun x => (f ‖x‖)⁻¹ • u x
    let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      radialQuotient_contDiffOn_puncturedBall
        (m + 3) R f u hfC1 hfpos huC1
    ContinuousOn
      (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s i => finiteBallSphereFamily_memLp
            (m + 3) R z hz s i) k))
      (uIcc δ R) := by
  dsimp only
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos huC1
  let b := vectorSphereRadialMean (m + 3)
    (finiteBallSphereFamily (m + 3) R z)
    (fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i) k
  by_cases hδlt : δ < R
  · have htrace :=
      actual_quotient_finiteBallSphereFamily_trace_tendsto_outer_left
        (m + 3) R hR f u hfC1 hfpos huC1 huBoundary k
    have hbCont : ContinuousOn b (Icc δ R) :=
      finiteBallSphereRadialMean_continuousOn_positive_annulus
        (m + 3) R δ hδ hδlt z hz k htrace
    exact bridgeOriginFlux_continuousOn_positive_annulus
      m f F b δ R hδ hδlt
      (fun r => hfC1.differentiable_one r) hFDiff hbCont
  · have hδEq : δ = R := le_antisymm hδR (le_of_not_gt hδlt)
    subst δ
    simpa only [uIcc_self] using
      (continuousOn_singleton (bridgeOriginFlux m f F b) R)

end

end BrezisOP6
