import BrezisOP6.ActualSmoothAnnularCoordinateFixed
import BrezisOP6.ActualAnnularDistanceIntegrability
import BrezisOP6.SphereBridgeFiniteSum

/-!
# Physical annular stability from the uniform spherical estimate

The coordinate constant is selected before the smooth competitor.  A
finite sum and the polar distance estimate then control the physical
distance on any compact annulus by the scalar bridge energies.
-/

namespace BrezisOP6

open Filter MeasureTheory Set Metric
open scoped Topology

noncomputable section

theorem actual_smooth_annular_distance_le_coordinate_bridge_uniform
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
        (hu : SmoothBallCompetitor m R p.f u),
        let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
          fun x => (p.f ‖x‖)⁻¹ • u x
        let hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
        let hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < p.f s :=
          fun s hs hsR => p.hfpos s ⟨hs, hsR⟩
        let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
          radialQuotient_contDiffOn_puncturedBall
            (m + 3) R p.f u hfC1 hfpos hu.1.contDiffOn
        let g := finiteBallSphereFamily (m + 3) R z
        let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
        let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
        (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
          ‖u x - radialVortex (m + 3) p.f x‖ ^ 2) ≤
          C * (∑ k : Fin (m + 3),
            ∫ r in (0 : ℝ)..R,
              scalarSphereBridgeDensity m p.f p.F
                (fun s y => (g s y) k)
                (fun s => hg s k) (fun s => dv s k) r) := by
  obtain ⟨C₀, hC₀, hcoordinate⟩ :=
    actual_smooth_annular_coordinate_stability_uniform
      m R p hLocal δ ρ hδ hδρ hρR
  have hRpow : 0 < R ^ (m + 2) := pow_pos p.hR _
  refine ⟨R ^ (m + 2) * C₀, mul_pos hRpow hC₀, ?_⟩
  intro u hu
  dsimp only
  have hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
  have hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < p.f s :=
    fun s hs hsR => p.hfpos s ⟨hs, hsR⟩
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (p.f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R p.f u hfC1 hfpos hu.1.contDiffOn
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let v := fun k : Fin (m + 3) => scalarSphereFamilyTrace (m + 3)
    (fun s y => (g s y) k) (fun s => hg s k)
  let q := fun k : Fin (m + 3) => ∫ r in (0 : ℝ)..R,
    scalarSphereBridgeDensity m p.f p.F
      (fun s y => (g s y) k) (fun s => hg s k) (fun s => dv s k) r
  have htrace (k : Fin (m + 3)) :
      (∫ r in δ..ρ, ‖v k r - v k R‖ ^ 2) ≤ C₀ * q k := by
    simpa only [v, q, z, g, hg, dv] using hcoordinate u hu k
  have hsum :
      (∑ k : Fin (m + 3),
        ∫ r in δ..ρ, ‖v k r - v k R‖ ^ 2) ≤
        C₀ * (∑ k : Fin (m + 3), q k) := by
    calc
      (∑ k : Fin (m + 3),
        ∫ r in δ..ρ, ‖v k r - v k R‖ ^ 2) ≤
          ∑ k : Fin (m + 3), C₀ * q k :=
        Finset.sum_le_sum (fun k _ => htrace k)
      _ = C₀ * (∑ k : Fin (m + 3), q k) := by
        rw [Finset.mul_sum]
  have hpolar := actual_annular_distance_le_trace_of_smooth
    (m + 3) (by omega) δ ρ R hδ hδρ hρR p.f u
    p.hfC2.continuous hu.1.continuous
    (fun r hr => p.hfpos r ⟨hr.1, hr.2.le⟩)
    (fun r hr => p.hflt r hr) hz
  have hpolar' :
      (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
        ‖u x - radialVortex (m + 3) p.f x‖ ^ 2) ≤
      R ^ (m + 2) *
        (∑ k : Fin (m + 3),
          ∫ r in δ..ρ, ‖v k r - v k R‖ ^ 2) := by
    have hpow : (m + 3) - 1 = m + 2 := by omega
    simpa only [hpow, v, z, g, hg] using hpolar
  calc
    (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
        ‖u x - radialVortex (m + 3) p.f x‖ ^ 2) ≤
        R ^ (m + 2) *
          (∑ k : Fin (m + 3),
            ∫ r in δ..ρ, ‖v k r - v k R‖ ^ 2) := hpolar'
    _ ≤ R ^ (m + 2) * (C₀ * ∑ k : Fin (m + 3), q k) :=
      mul_le_mul_of_nonneg_left hsum hRpow.le
    _ = (R ^ (m + 2) * C₀) *
        (∑ k : Fin (m + 3), q k) := by ring

/-- The finite scalar bridge sum is exactly the vector bridge appearing
in the energy identity.  This final form has one physical annular
distance and one vector-valued bridge energy. -/
theorem actual_smooth_annular_distance_le_vector_bridge_uniform
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
        (hu : SmoothBallCompetitor m R p.f u),
        let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
          fun x => (p.f ‖x‖)⁻¹ • u x
        let hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
        let hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < p.f s :=
          fun s hs hsR => p.hfpos s ⟨hs, hsR⟩
        let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
          radialQuotient_contDiffOn_puncturedBall
            (m + 3) R p.f u hfC1 hfpos hu.1.contDiffOn
        let g := finiteBallSphereFamily (m + 3) R z
        let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
        let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
        (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
          ‖u x - radialVortex (m + 3) p.f x‖ ^ 2) ≤
          C * (∫ r in (0 : ℝ)..R,
            vectorSphereBridgeDensity m p.f p.F g hg dv r) := by
  obtain ⟨C, hC, hcoordinate⟩ :=
    actual_smooth_annular_distance_le_coordinate_bridge_uniform
      m R p hLocal δ ρ hδ hδρ hρR
  refine ⟨C, hC, ?_⟩
  intro u hu
  dsimp only
  have hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 p.F := p.hFC2.of_le (by norm_num)
  have hdfC1 : ContDiff ℝ 1 (deriv p.f) :=
    radial_profile_deriv_contDiff_one p.f p.hfC2
  have hHf0 : p.Hf 0 ≠ 0 := by
    rw [p.hHf0]
    exact ne_of_gt p.hβ
  have hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < p.f s :=
    fun s hs hsR => p.hfpos s ⟨hs, hsR⟩
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (p.f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R p.f u hfC1 hfpos hu.1.contDiffOn
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  have hfullInt (k : Fin (m + 3)) : IntervalIntegrable
      (scalarSphereBridgeDensity m p.f p.F
        (fun s y => (g s y) k) (fun s => hg s k)
        (fun s => dv s k)) volume 0 R := by
    simpa only [g, hg, dv, z] using
      (actual_finiteBall_scalarBridge_intervalIntegrable
        m R p.hR p.f p.F p.Hf u hfC1 hdfC1 hFC1 p.hHf
        hu.1 hHf0 p.hfFactor hfpos
        (fun r hr => (p.profile_gap_positive m R r
          ⟨hr.1, hr.2.le⟩).le) k)
  have hsum := vectorSphereBridge_integral_eq_coordinate_sum
    m p.f p.F R g hg dv hfullInt
  have hbound := hcoordinate u hu
  simpa only [z, g, hg, dv, hsum] using hbound

end

end BrezisOP6
