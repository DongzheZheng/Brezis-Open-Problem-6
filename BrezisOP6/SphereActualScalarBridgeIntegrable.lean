import BrezisOP6.SphereScalarBridgeMeasurable
import BrezisOP6.SphereScalarBridgeGrowth
import BrezisOP6.EnergyGlobalWeightedBounds
import BrezisOP6.EnergyQuotientPuncturedC1

/-!
# Integrability of each actual spherical bridge coordinate

The closed-ball `C¹` bounds and the regular radial profile give a global
inverse-square estimate for the quotient.  The polar scalar bridge is
therefore (O(r^m)) near the origin and is measurable by the punctured
`C¹` construction.  Its interval integral is an ordinary Lebesgue
integral, with no formal integrability assumption on a coordinate mode.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem actual_finiteBall_scalarBridge_intervalIntegrable
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F H : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hFC1 : ContDiff ℝ 1 F)
    (hH : ContDiff ℝ 1 H)
    (huC1 : ContDiff ℝ 1 u)
    (hH0 : H 0 ≠ 0)
    (hf : ∀ r, 0 < r → r ≤ R → f r = r * H (r ^ 2))
    (hfpos : ∀ r, 0 < r → r ≤ R → 0 < f r)
    (hd0 : ∀ r ∈ Ioo (0 : ℝ) R,
      0 ≤ f r ^ 2 - F r ^ 2)
    (k : Fin (m + 3)) :
    let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
      fun x => (f ‖x‖)⁻¹ • u x
    let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      radialQuotient_contDiffOn_puncturedBall
        (m + 3) R f u hfC1 hfpos huC1.contDiffOn
    IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      volume 0 R := by
  dsimp only
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos huC1.contDiffOn
  obtain ⟨A, B, C, hA, hB, hC, hbounds⟩ :=
    actual_quotient_global_weighted_bounds m R hR f H u
      hfC1 hdfC1 hH huC1 hH0 hf hfpos
  have hdle (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      f r ^ 2 - F r ^ 2 ≤ f r ^ 2 := by
    nlinarith [sq_nonneg (F r)]
  have hG (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
      (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1) :
      f r ^ 2 * euclideanGradientSq (m + 3) z
        (r • (ω : GLEuclidean (m + 3))) ≤
          A + B * r⁻¹ ^ 2 := by
    have hω : ‖(ω : GLEuclidean (m + 3))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    have hnorm : ‖r • (ω : GLEuclidean (m + 3))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
      ring
    have h := (hbounds (r • (ω : GLEuclidean (m + 3)))
      (by simpa only [hnorm] using hr.1)
      (by simpa only [hnorm] using hr.2)).1
    simpa only [hnorm, z] using h
  have hZ (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
      (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1) :
      f r ^ 2 * ‖z (r • (ω : GLEuclidean (m + 3)))‖ ^ 2 ≤ C := by
    have hω : ‖(ω : GLEuclidean (m + 3))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    have hnorm : ‖r • (ω : GLEuclidean (m + 3))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
      ring
    have h := (hbounds (r • (ω : GLEuclidean (m + 3)))
      (by simpa only [hnorm] using hr.1)
      (by simpa only [hnorm] using hr.2)).2
    simpa only [hnorm, z] using h
  have hMeas := finiteBall_scalarBridge_aestronglyMeasurable
    m f F R z hz
      hfC1.continuous.continuousOn
      hFC1.continuous.continuousOn k
  exact finiteBall_scalarBridge_intervalIntegrable_of_weighted_bounds
    m f F R hR z hz k A B C hA hB hC hd0 hdle hG hZ hMeas

end

end BrezisOP6
