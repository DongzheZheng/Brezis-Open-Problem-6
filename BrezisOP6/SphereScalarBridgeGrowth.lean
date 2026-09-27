import BrezisOP6.SphereScalarBridgeSurface
import BrezisOP6.SphereRadialGrowthIntegrability

/-!
# Coordinatewise bridge integrability from weighted quotient bounds

The scalar surface identity turns the pointwise polynomial majorant into
an ordinary interval-integrable bound for each target coordinate.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem finiteBall_scalarBridge_intervalIntegrable_of_weighted_bounds
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin (m + 3)) (A B C : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd0 : ∀ r ∈ Ioo (0 : ℝ) R,
      0 ≤ f r ^ 2 - F r ^ 2)
    (hdle : ∀ r ∈ Ioo (0 : ℝ) R,
      f r ^ 2 - F r ^ 2 ≤ f r ^ 2)
    (hG : ∀ r ∈ Ioo (0 : ℝ) R,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        f r ^ 2 * euclideanGradientSq (m + 3) z
          (r • (ω : GLEuclidean (m + 3))) ≤
        A + B * r⁻¹ ^ 2)
    (hZ : ∀ r ∈ Ioo (0 : ℝ) R,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        f r ^ 2 * ‖z (r • (ω : GLEuclidean (m + 3)))‖ ^ 2 ≤ C)
    (hMeas : AEStronglyMeasurable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      (volume.restrict (Ioc (0 : ℝ) R))) :
    IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      volume 0 R := by
  let μ := unitSphereMeasure (m + 3)
  let M := μ.real Set.univ
  let Q := scalarSphereBridgeDensity m f F
    (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
    (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
    (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)
  let T : ℝ := A * R ^ 2 + B + (m + 2 : ℝ) * C
  let Ctotal : ℝ := M * T
  have hM : 0 ≤ M := measureReal_nonneg
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hCtotal : 0 ≤ Ctotal := mul_nonneg hM hT
  have hbound (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      |Q r| ≤ Ctotal * r ^ m := by
    let q : Metric.sphere (0 : GLEuclidean (m + 3)) 1 → ℝ :=
      scalarSphereBridgePointwise m f F
        (fun s y => (z (s • y)) k) r
    have hqInt : Integrable q μ := by
      apply (finiteBallSphereFamily_scalarBridgePointwise_integrable
        m f F R z hz r hr k).congr
      filter_upwards [] with ω
      exact finiteBallSphereFamily_scalarBridgePointwise_eq_actual
        m f F R z r hr ω k
    have hzr (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1) :
        DifferentiableAt ℝ z (r • (ω : GLEuclidean (m + 3))) := by
      have hx : r • (ω : GLEuclidean (m + 3)) ∈
          {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} := by
        have hω : ‖(ω : GLEuclidean (m + 3))‖ = 1 :=
          mem_sphere_zero_iff_norm.mp ω.property
        have hnorm : ‖r • (ω : GLEuclidean (m + 3))‖ = r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
          ring
        change 0 < ‖r • (ω : GLEuclidean (m + 3))‖ ∧
          ‖r • (ω : GLEuclidean (m + 3))‖ < R
        rw [hnorm]
        exact hr
      have hopen : IsOpen
          {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} :=
        (isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)
      exact (hz.differentiableOn_one).differentiableAt
        (hopen.mem_nhds hx)
    have hqBound (ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1) :
        |q ω| ≤ r ^ m *
          (A * r ^ 2 + B + (m + 2 : ℝ) * C) :=
      scalarSphereBridgePointwise_abs_le_power
        m f F z r ω k A B C hr.1 (hzr ω)
        (hd0 r hr) (hdle r hr)
        hA hB hC (hG r hr ω) (hZ r hr ω)
    have hIntBound :
        (∫ ω, |q ω| ∂μ) ≤
          ∫ _ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
            r ^ m * (A * r ^ 2 + B + (m + 2 : ℝ) * C) ∂μ := by
      apply integral_mono hqInt.abs (integrable_const _)
      intro ω
      exact hqBound ω
    have hQeq : Q r = ∫ ω, q ω ∂μ :=
      finiteBallSphereFamily_scalarBridgeDensity_eq_actual_surface_integral
        m f F R z hz r hr k
    have hnorm :
        |Q r| ≤ M * (r ^ m *
          (A * r ^ 2 + B + (m + 2 : ℝ) * C)) := by
      rw [hQeq]
      have htri : |∫ ω, q ω ∂μ| ≤ ∫ ω, |q ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm q
      have hconst :
          (∫ _ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
            r ^ m * (A * r ^ 2 + B + (m + 2 : ℝ) * C) ∂μ) =
          M * (r ^ m *
            (A * r ^ 2 + B + (m + 2 : ℝ) * C)) := by
        simp [M, μ, smul_eq_mul]
      linarith [hIntBound, hconst]
    have hrSq : r ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ hr.1.le hR.le).2 hr.2.le
    have hTbound :
        A * r ^ 2 + B + (m + 2 : ℝ) * C ≤ T := by
      dsimp [T]
      nlinarith [mul_le_mul_of_nonneg_left hrSq hA]
    have hpow : 0 ≤ r ^ m := pow_nonneg hr.1.le m
    have hmul := mul_le_mul_of_nonneg_left hTbound
      (mul_nonneg hM hpow)
    dsimp [Ctotal]
    nlinarith [hnorm, hmul]
  have hRnull : ∀ᵐ r : ℝ ∂volume, r ≠ R := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      (measure_singleton R : volume {R} = 0)
  have hboundAE :
      ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) R)),
        |Q r| ≤ Ctotal * r ^ m := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hRnull] with r hr hrNe
    exact hbound r ⟨hr.1, lt_of_le_of_ne hr.2 hrNe⟩
  exact intervalIntegrable_of_ae_abs_le_power
    m R Ctotal Q hR.le hCtotal hMeas hboundAE

end

end BrezisOP6
