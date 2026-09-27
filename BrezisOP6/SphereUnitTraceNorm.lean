import BrezisOP6.SphereL2NormIntegral
import BrezisOP6.SphereBridgePolarSpatial
import BrezisOP6.SphereFiniteFamily

/-!
# The total sphere `L²` norm of a vector trace

The sum of coordinate `L²` norms is the surface integral of the squared
Euclidean norm.  A unit-sphere-valued field therefore has the same total
`L²` norm as the identity trace, regardless of its angular dependence.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

theorem vectorSphereTrace_total_norm_sq_eq_integral
    (n : ℕ) (g : GLEuclidean n → GLEuclidean n)
    (hg : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (g ω) k) 2 (unitSphereMeasure n))
    (hcont : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g ω)) :
    vectorSphereL2Sq n (vectorSphereTrace n g hg) =
      ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        ‖g ω‖ ^ 2 ∂(unitSphereMeasure n) := by
  have hInt (k : Fin n) : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        ((g ω) k) ^ 2) (unitSphereMeasure n) := by
    have hc : Continuous (fun ω : Metric.sphere
        (0 : GLEuclidean n) 1 => (g ω) k) :=
      (EuclideanSpace.proj k).continuous.comp hcont
    exact (hc.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold vectorSphereL2Sq vectorSphereTrace
  simp_rw [unitSphereTrace_norm_sq_eq_integral]
  calc
    (∑ k : Fin n, ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ((g ω) k) ^ 2 ∂(unitSphereMeasure n)) =
        ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          (∑ k : Fin n, ((g ω) k) ^ 2) ∂(unitSphereMeasure n) := by
          rw [integral_finset_sum]
          intro k _
          exact hInt k
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (sphereVector_norm_sq_eq_sum_coords n (g ω)).symm

theorem vectorSphereTrace_total_norm_sq_eq_of_unit_fields
    (n : ℕ) (g h : GLEuclidean n → GLEuclidean n)
    (hg : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (g ω) k) 2 (unitSphereMeasure n))
    (hh : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (h ω) k) 2 (unitSphereMeasure n))
    (hgc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g ω))
    (hhc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => h ω))
    (hunitg : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ‖g ω‖ = 1)
    (hunith : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ‖h ω‖ = 1) :
    vectorSphereL2Sq n (vectorSphereTrace n g hg) =
      vectorSphereL2Sq n (vectorSphereTrace n h hh) := by
  rw [vectorSphereTrace_total_norm_sq_eq_integral n g hg hgc,
    vectorSphereTrace_total_norm_sq_eq_integral n h hh hhc]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [hunitg ω, hunith ω]

/-- The interior slice of a punctured `C¹` finite-ball family is a
continuous field on the compact unit sphere. -/
theorem finiteBallSphereFamily_interior_continuous
    (n : ℕ) (R : ℝ) (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) R) :
    Continuous (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      finiteBallSphereFamily n R z r ω) := by
  have hRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        r • (ω : GLEuclidean n)) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have hMaps : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      r • (ω : GLEuclidean n) ∈
        {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    intro ω
    have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    have hnorm : ‖r • (ω : GLEuclidean n)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
      ring
    change 0 < ‖r • (ω : GLEuclidean n)‖ ∧
      ‖r • (ω : GLEuclidean n)‖ < R
    rw [hnorm]
    exact hr
  simpa only [finiteBallSphereFamily_interior n R z r hr] using
    hz.continuousOn.comp_continuous hRay hMaps

theorem finiteBallSphereFamily_outer_continuous
    (n : ℕ) (R : ℝ) (z : GLEuclidean n → GLEuclidean n) :
    Continuous (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      finiteBallSphereFamily n R z R ω) := by
  simpa only [finiteBallSphereFamily_outer] using
    (continuous_subtype_val : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (ω : GLEuclidean n)))

/-- The actual quotient sphere has the same total coordinate `L²` norm
as the identity boundary sphere whenever the quotient is sphere-valued. -/
theorem finiteBallSphereFamily_total_norm_eq_outer
    (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hunit : ∀ x : GLEuclidean n,
      0 < ‖x‖ → ‖x‖ < R → ‖z x‖ ^ 2 = 1)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) R) :
    vectorSphereL2Sq n
      (fun k => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r) =
    vectorSphereL2Sq n
      (fun k => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) R) := by
  have hRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        r • (ω : GLEuclidean n)) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have hMaps : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      r • (ω : GLEuclidean n) ∈
        {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    intro ω
    have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    have hnorm : ‖r • (ω : GLEuclidean n)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
      ring
    change 0 < ‖r • (ω : GLEuclidean n)‖ ∧
      ‖r • (ω : GLEuclidean n)‖ < R
    rw [hnorm]
    exact hr
  have hgc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => finiteBallSphereFamily n R z r ω) := by
    simpa only [finiteBallSphereFamily_interior n R z r hr] using
      hz.continuousOn.comp_continuous hRay hMaps
  have hhc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => finiteBallSphereFamily n R z R ω) := by
    simpa only [finiteBallSphereFamily_outer] using
      (continuous_subtype_val : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          (ω : GLEuclidean n)))
  have hunitg (ω : Metric.sphere (0 : GLEuclidean n) 1) :
      ‖finiteBallSphereFamily n R z r ω‖ = 1 := by
    rw [finiteBallSphereFamily_interior n R z r hr]
    have hx := hMaps ω
    have hsq := hunit (r • (ω : GLEuclidean n)) hx.1 hx.2
    nlinarith [norm_nonneg (z (r • (ω : GLEuclidean n)))]
  have hunith (ω : Metric.sphere (0 : GLEuclidean n) 1) :
      ‖finiteBallSphereFamily n R z R ω‖ = 1 := by
    rw [finiteBallSphereFamily_outer]
    exact mem_sphere_zero_iff_norm.mp ω.property
  have h := vectorSphereTrace_total_norm_sq_eq_of_unit_fields
    n (finiteBallSphereFamily n R z r)
    (finiteBallSphereFamily n R z R)
    (fun k => finiteBallSphereFamily_memLp n R z hz r k)
    (fun k => finiteBallSphereFamily_memLp n R z hz R k)
    hgc hhc hunitg hunith
  exact h

end

end BrezisOP6
