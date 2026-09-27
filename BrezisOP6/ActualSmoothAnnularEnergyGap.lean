import BrezisOP6.ActualSmoothAnnularDistanceUniform
import BrezisOP6.ActualSmoothQuantitativeBridge

/-!
# Uniform physical annular stability by the smooth energy gap

The contact and angular remainders control the distance on each compact
annulus.  The full two-profile bridge is bounded by the physical energy
gap, so the annular constant is selected once before the competitor.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

theorem actual_smooth_annular_energy_gap_uniform
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
        (hu : SmoothBallCompetitor m R p.f u),
        (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
          ‖u x - radialVortex (m + 3) p.f x‖ ^ 2) ≤
          C * (euclideanBallEnergy (m + 3) R u -
            euclideanBallEnergy (m + 3) R
              (radialVortex (m + 3) p.f)) := by
  obtain ⟨C₀, hC₀, hdist⟩ :=
    actual_smooth_annular_distance_le_coordinate_bridge_uniform
      m R p hLocal δ ρ hδ hδρ hρR
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro u hu
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (p.f ‖x‖)⁻¹ • u x
  have hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
  have hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < p.f s :=
    fun s hs hsR => p.hfpos s ⟨hs, hsR⟩
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R p.f u hfC1 hfpos hu.1.contDiffOn
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let S := ∑ k : Fin (m + 3),
    ∫ r in (0 : ℝ)..R,
      scalarSphereBridgeDensity m p.f p.F
        (fun s y => (g s y) k)
        (fun s => hg s k) (fun s => dv s k) r
  have hdistance :
      (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
        ‖u x - radialVortex (m + 3) p.f x‖ ^ 2) ≤ C₀ * S := by
    simpa only [S, z, g, hg, dv] using hdist u hu
  have hbridge : S ≤
      2 * (euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) p.f)) := by
    simpa only [S, z, g, hg, dv, radialQuotientField] using
      p.smooth_coordinate_bridge_sum_le_two_energy_gap
        m R hPublished u hu
  calc
    (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
        ‖u x - radialVortex (m + 3) p.f x‖ ^ 2) ≤ C₀ * S :=
      hdistance
    _ ≤ C₀ * (2 * (euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) p.f))) :=
      mul_le_mul_of_nonneg_left hbridge hC₀.le
    _ = (2 * C₀) * (euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) p.f)) := by ring

end

end BrezisOP6
