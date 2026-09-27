import BrezisOP6.EnergyActualInteriorPair
import BrezisOP6.EnergyActualSphereMinimum
import BrezisOP6.EnergyBridgeQuantitative
import BrezisOP6.SphereBridgeFiniteSum
import BrezisOP6.SphereBridgeFullBallEquality
import BrezisOP6.SphereFiniteFamilyNonnegative
import BrezisOP6.SphereActualScalarBridgeIntegrable
import BrezisOP6.EnergyConcreteQuartic
import BrezisOP6.PhysicalRadialContactData
import BrezisOP6.ProfileOrderToBridge

/-!
# Quantitative bridge for the physical smooth competitor

The coordinate bridge densities below are the actual spherical slices of
`u / f`.  The published whole-space vortex minimum bounds the full
two-profile bridge; the nonnegative quartic remainder then bounds the sum
of all coordinate quadratic bridges by twice the physical energy gap.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

set_option maxHeartbeats 2000000

theorem actual_smooth_coordinate_bridge_sum_le_two_energy_gap
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hfData : SmoothProfileBallInteriorData m f
      (radialQuotientField (m + 3) f u) R ρf Bf)
    (hFData : SmoothProfileBallInteriorData m F
      (radialQuotientField (m + 3) f u) R ρF BF)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α) (hβ : 0 < β)
    (hfC1 : ContDiff ℝ 1 f)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hFC1 : ContDiff ℝ 1 F)
    (huC1 : ContDiff ℝ 1 u)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hd0 : ∀ r ∈ Ioo (0 : ℝ) R,
      0 ≤ f r ^ 2 - F r ^ 2)
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖) :
    (∑ k : Fin (m + 3),
      ∫ r in (0 : ℝ)..R,
        scalarSphereBridgeDensity m f F
          (fun s y => (finiteBallSphereFamily (m + 3) R
            (radialQuotientField (m + 3) f u) s y) k)
          (fun s => finiteBallSphereFamily_memLp (m + 3) R
            (radialQuotientField (m + 3) f u)
            (radialQuotient_contDiffOn_puncturedBall (m + 3) R
              f u hfC1 hfpos huC1.contDiffOn) s k)
          (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R
            (radialQuotientField (m + 3) f u)
            (radialQuotient_contDiffOn_puncturedBall (m + 3) R
              f u hfC1 hfpos huC1.contDiffOn) s k) r)
      ≤ 2 * (euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) f)) := by
  let z := radialQuotientField (m + 3) f u
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos huC1.contDiffOn
  have hfullInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      volume 0 R := by
    intro k
    simpa only [z, radialQuotientField] using
      actual_finiteBall_scalarBridge_intervalIntegrable
        m R hR f F Hf u hfC1 hdfC1 hFC1 hHf huC1
        (by rw [hHf0]; exact ne_of_gt hβ)
        hfFactor hfpos hd0 k
  have hvectorInt := finiteBallSphereBridge_intervalIntegrable_of_coordinates
    m f F R z hz hfullInt
  have hquarticInt : Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) :=
    euclideanQuarticBridgeDensity_actual_quotient_integrable
      m R f F Hf HF α β u hβ hHf0 hHF0 hfFactor hFFactor
      hfpos hHf hHF hfC1.continuous hFC1.continuous
      huC1.contDiffOn
  have hfInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R f z hfData.reduced_density_integrable
  have hFInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R F z hFData.reduced_density_integrable
  have hbridgeInt := bridgeEnergyDensity_integrable_of_single
    m R f F z hfInt hFInt
  have hquadInt := euclideanQuadraticBridgeDensity_integrable_of_bridge_quartic
    m R f F z hbridgeInt hquarticInt
  have hbridgeLe := euclideanBall_energy_gap_ge_bridge_of_regular_competitor
    m R hR f F Hf HF α β u ρf Bf ρF BF
    hfData hFData hPublished hHf hHF hHf0 hHF0 hβ
    hfFactor hFFactor hfpos huC1.contDiffOn huBoundary
  have hquadLe := quadraticBridgeIntegral_le_two_energy_gap
    m R f F z u hquadInt hquarticInt hFnonneg hFle hbridgeLe
  have hballEq := euclideanQuadraticBridge_ball_integral_eq_finiteFamily
    m f F R hR z hz hquadInt hvectorInt
  have hsumEq := vectorSphereBridge_integral_eq_coordinate_sum
    m f F R (finiteBallSphereFamily (m + 3) R z)
    (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
    (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) hfullInt
  rw [hballEq, hsumEq] at hquadLe
  simpa only [z, radialQuotientField] using hquadLe

/-- The same quantitative estimate with all interior identities and sign
conditions constructed from the physical radial data.  The constant `2`
is universal and independent of the smooth competitor. -/
theorem PhysicalRadialData.smooth_coordinate_bridge_sum_le_two_energy_gap
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hu : SmoothBallCompetitor m R p.f u) :
    (∑ k : Fin (m + 3),
      ∫ r in (0 : ℝ)..R,
        scalarSphereBridgeDensity m p.f p.F
          (fun s y => (finiteBallSphereFamily (m + 3) R
            (radialQuotientField (m + 3) p.f u) s y) k)
          (fun s => finiteBallSphereFamily_memLp (m + 3) R
            (radialQuotientField (m + 3) p.f u)
            (radialQuotient_contDiffOn_puncturedBall (m + 3) R
              p.f u (p.hfC2.of_le (by norm_num))
              (fun t ht htR => p.hfpos t ⟨ht, htR⟩)
              hu.1.contDiffOn) s k)
          (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R
            (radialQuotientField (m + 3) p.f u)
            (radialQuotient_contDiffOn_puncturedBall (m + 3) R
              p.f u (p.hfC2.of_le (by norm_num))
              (fun t ht htR => p.hfpos t ⟨ht, htR⟩)
              hu.1.contDiffOn) s k) r)
      ≤ 2 * (euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) p.f)) := by
  have hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 p.F := p.hFC2.of_le (by norm_num)
  have hdfC1 : ContDiff ℝ 1 (deriv p.f) :=
    radial_profile_deriv_contDiff_one p.f p.hfC2
  have hdFC1 : ContDiff ℝ 1 (deriv p.F) :=
    radial_profile_deriv_contDiff_one p.F p.hFC2
  have hfpos : ∀ t : ℝ, 0 < t → t ≤ R → 0 < p.f t :=
    fun t ht htR => p.hfpos t ⟨ht, htR⟩
  have hFleRad : ∀ t : ℝ, 0 < t → t ≤ R →
      0 ≤ p.F t ∧ p.F t ≤ p.f t := by
    intro t ht htR
    exact ⟨(p.hFposAll t ht).le,
      (p.profile_order m R t ⟨ht, htR⟩).le⟩
  obtain ⟨ρ, BfFlux, BFFlux, hfData, hFData⟩ :=
    actual_smooth_competitor_has_paired_interior_data
      m R p.hR p.f p.F p.Hf p.HF
      p.β p.α p.Af p.Bf p.AF p.BF u
      (p.hfTaylor.toClosed p.hR) (p.hFTaylor.toClosed p.hR)
      p.hf0 p.hF0 p.hβ p.hα p.hHf0
      hfC1 hFC1 hdfC1 hdFC1 hu.1 p.hHf p.hHF
      hfpos hFleRad p.hfFactor p.hFFactor p.hfODE
      (fun t ht _ => p.hFodeAll t ht)
  obtain ⟨_, hdpos, hFnonneg, hFle, _⟩ :=
    bridge_signs_of_strict_profile_order
      m R p.f p.F p.hf0 p.hF0
      (fun t ht => p.hFposAll t ht.1)
      (p.profile_order m R)
  have hbase := actual_smooth_coordinate_bridge_sum_le_two_energy_gap
    m R p.hR p.f p.F p.Hf p.HF p.α p.β u
    ρ BfFlux ρ BFFlux hfData hFData hPublished
    p.hHf p.hHF p.hHf0 p.hHF0 p.hβ
    hfC1 hdfC1 hFC1 hu.1 p.hfFactor p.hFFactor
    hfpos hu.2 (fun t ht => (hdpos t ht).le)
    hFnonneg hFle
  simpa only using hbase

end

end BrezisOP6
