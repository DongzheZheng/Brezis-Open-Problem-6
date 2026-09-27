import BrezisOP6.SphereTraceDifferenceNorm
import BrezisOP6.SphereAnnulusRadiusOuter
import BrezisOP6.SphereFiniteFamily

/-!
# From spherical trace distances to an actual annular distance

The radial stability estimate controls a sum of `L²` distances between
coordinate traces.  These lemmas identify that sum with the physical
squared distance on each sphere and then with the distance between the
competitor and the radial vortex.  This is the geometric bridge needed
to pass equality through strong Sobolev approximation.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem finiteBallSphereFamily_trace_distance_eq_surface
    (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    (∑ k : Fin n,
      ‖scalarSphereFamilyTrace n
          (fun s y => (finiteBallSphereFamily n R z s y) k)
          (fun s => finiteBallSphereFamily_memLp n R z hz s k) r -
        scalarSphereFamilyTrace n
          (fun s y => (finiteBallSphereFamily n R z s y) k)
          (fun s => finiteBallSphereFamily_memLp n R z hz s k) R‖ ^ 2) =
      ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        ‖z (r • (ω : GLEuclidean n)) - (ω : GLEuclidean n)‖ ^ 2
          ∂(unitSphereMeasure n) := by
  let g := finiteBallSphereFamily n R z r
  let h := finiteBallSphereFamily n R z R
  have hg := fun k => finiteBallSphereFamily_memLp n R z hz r k
  have hh := fun k => finiteBallSphereFamily_memLp n R z hz R k
  have hc := finiteBallSphereFamily_interior_continuous n R z hz r hr
  have hc' := finiteBallSphereFamily_outer_continuous n R z
  have hmain := vectorSphereTrace_difference_norm_sq_eq_integral
    n g h hg hh hc hc'
  simpa only [g, h, vectorSphereTrace, scalarSphereFamilyTrace,
    finiteBallSphereFamily_interior n R z r hr,
    finiteBallSphereFamily_outer] using hmain

theorem actual_sphere_distance_eq_factor_trace
    (n : ℕ) (f : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (r : ℝ) (hr : 0 < r)
    (hfr : f r ≠ 0)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) :
    ‖u (energySphereRay n ω r) -
      radialVortex n f (energySphereRay n ω r)‖ ^ 2 =
      f r ^ 2 *
        ‖(f ‖energySphereRay n ω r‖)⁻¹ •
            u (energySphereRay n ω r) - (ω : GLEuclidean n)‖ ^ 2 := by
  let x := energySphereRay n ω r
  have hx : ‖x‖ = r := energySphereRay_norm n ω r hr.le
  have hu : f r • ((f ‖x‖)⁻¹ • u x) = u x := by
    rw [hx, smul_smul, mul_inv_cancel₀ hfr, one_smul]
  have hv : radialVortex n f x = f r • (ω : GLEuclidean n) := by
    unfold radialVortex
    rw [hx]
    change (f r / r) • (r • (ω : GLEuclidean n)) = _
    rw [smul_smul]
    congr 1
    field_simp [ne_of_gt hr]
  calc
    ‖u x - radialVortex n f x‖ ^ 2 =
        ‖f r • ((f ‖x‖)⁻¹ • u x - (ω : GLEuclidean n))‖ ^ 2 := by
          rw [smul_sub, hu, hv]
    _ = f r ^ 2 *
          ‖(f ‖x‖)⁻¹ • u x - (ω : GLEuclidean n)‖ ^ 2 := by
          rw [norm_smul, mul_pow]
          simp only [Real.norm_eq_abs, sq_abs]

/-- On a compact interior annulus the physical squared distance to the
vortex is exactly the polar Jacobian, the squared profile, and the sum of
coordinate `L²` trace distances.  No equality-case regularity is assumed. -/
theorem actual_annular_distance_eq_weighted_trace
    (n : ℕ) (hn : 1 ≤ n) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (f : ℝ → ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hfne : ∀ r ∈ Ioo (0 : ℝ) R, f r ≠ 0)
    (hz : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (f ‖x‖)⁻¹ • u x)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hAnnInt : IntegrableOn
      (fun x : GLEuclidean n =>
        ‖u x - radialVortex n f x‖ ^ 2)
      (energyPositiveAnnulus n δ ρ) volume) :
    (∫ x in energyPositiveAnnulus n δ ρ,
        ‖u x - radialVortex n f x‖ ^ 2) =
      ∫ r in δ..ρ, r ^ (n - 1) * f r ^ 2 *
        (∑ k : Fin n,
          ‖scalarSphereFamilyTrace n
              (fun s y => (finiteBallSphereFamily n R
                (fun x => (f ‖x‖)⁻¹ • u x) s y) k)
              (fun s => finiteBallSphereFamily_memLp n R
                (fun x => (f ‖x‖)⁻¹ • u x) hz s k) r -
            scalarSphereFamilyTrace n
              (fun s y => (finiteBallSphereFamily n R
                (fun x => (f ‖x‖)⁻¹ • u x) s y) k)
              (fun s => finiteBallSphereFamily_memLp n R
                (fun x => (f ‖x‖)⁻¹ • u x) hz s k) R‖ ^ 2) := by
  let z : GLEuclidean n → GLEuclidean n :=
    fun x => (f ‖x‖)⁻¹ • u x
  let h : GLEuclidean n → ℝ :=
    fun x => ‖u x - radialVortex n f x‖ ^ 2
  have hPolarInt := annulus_polar_indicator_integrable_of_integrableOn
    n hn δ ρ hδρ h hAnnInt
  rw [annulus_integral_eq_interval_sphere_integral
    n hn δ ρ hδ hδρ h hPolarInt]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc δ ρ := by
    simpa only [uIcc_of_le hδρ] using hr
  have hrpos : 0 < r := lt_of_lt_of_le hδ hr'.1
  have hrR : r < R := lt_of_le_of_lt hr'.2 hρR
  have htrace := finiteBallSphereFamily_trace_distance_eq_surface
    n R z hz r ⟨hrpos, hrR⟩
  have hsurface :
      (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        h (energySphereRay n ω r) ∂(unitSphereMeasure n)) =
      f r ^ 2 *
        (∑ k : Fin n,
          ‖scalarSphereFamilyTrace n
              (fun s y => (finiteBallSphereFamily n R z s y) k)
              (fun s => finiteBallSphereFamily_memLp n R z hz s k) r -
            scalarSphereFamilyTrace n
              (fun s y => (finiteBallSphereFamily n R z s y) k)
              (fun s => finiteBallSphereFamily_memLp n R z hz s k) R‖ ^ 2) := by
    rw [htrace]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact actual_sphere_distance_eq_factor_trace n f u r hrpos
      (hfne r ⟨hrpos, hrR⟩) ω
  change r ^ (n - 1) * (∫ ω, h (energySphereRay n ω r)
    ∂(unitSphereMeasure n)) = _
  rw [hsurface]
  ring

end

end BrezisOP6
