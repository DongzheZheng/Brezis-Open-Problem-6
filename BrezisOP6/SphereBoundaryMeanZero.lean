import BrezisOP6.SphereBridgeIntegral
import BrezisOP6.SphereTraceGradient

/-!
# Vanishing mean of the identity boundary trace

The boundary term in the Picone calculation is the radial mean of the
quotient field. When the quotient's sphere trace is the identity, its
vanishing follows from antipodal symmetry of the concrete surface measure.
The symmetry statement is exposed separately and proved for `volume.toSphere`
in `SphereCoordinateOddness`.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

/-- The concrete sphere's coordinate-oddness fact, isolated from the PDE
bridge. Its unconditional proof is `unitSphereCoordinateMeanZero_actual` in
`SphereCoordinateOddness`. -/
def UnitSphereCoordinateMeanZero (n : ℕ) : Prop :=
  ∀ k : Fin n,
    (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ((ω : GLEuclidean n) k) ∂(unitSphereMeasure n)) = 0

/-- An identity boundary trace forces every regularized spherical mean
coefficient at the outer radius to vanish. -/
theorem vectorSphereRadialMean_boundary_zero_of_identity_trace
    (n : ℕ) (R : ℝ)
    (hOdd : UnitSphereCoordinateMeanZero n)
    (z : GLEuclidean n → GLEuclidean n)
    (hg : ∀ (s : ℝ) (k : Fin n),
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (z (s • (ω : GLEuclidean n))) k) 2
        (unitSphereMeasure n))
    (hBoundary : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      z (R • (ω : GLEuclidean n)) = (ω : GLEuclidean n))
    (k : Fin n) :
    vectorSphereRadialMean n (fun s y => z (s • y)) hg k R = 0 := by
  have hInt :
      (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (z (R • (ω : GLEuclidean n))) k
          ∂(unitSphereMeasure n)) = 0 := by
    calc
      _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ((ω : GLEuclidean n) k) ∂(unitSphereMeasure n) := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hBoundary ω]
      _ = 0 := hOdd k
  have hMean :
      sphereMeanCoefficient n
        (scalarSphereFamilyTrace n
          (fun s y => (z (s • y)) k) (fun s => hg s k) R) = 0 := by
    rw [sphereMeanCoefficient_eq_integral]
    have hTraceInt :
        (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          (scalarSphereFamilyTrace n
            (fun s y => (z (s • y)) k) (fun s => hg s k) R) ω
              ∂(unitSphereMeasure n)) =
        ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          (z (R • (ω : GLEuclidean n))) k
            ∂(unitSphereMeasure n) := by
      apply integral_congr_ae
      filter_upwards [(hg R k).coeFn_toLp] with ω hω
      exact hω
    rw [hTraceInt, hInt]
    ring
  unfold vectorSphereRadialMean scalarSphereRadialMean
  rw [hMean]
  ring

/-- The same boundary conclusion for a radius-indexed sphere family.
This is the form used by the explicit finite-ball family, whose values
away from the physical interval are chosen only to ensure `L²` membership. -/
theorem vectorSphereRadialMean_boundary_zero_of_identity_family
    (n : ℕ) (R : ℝ)
    (hOdd : UnitSphereCoordinateMeanZero n)
    (g : ℝ → GLEuclidean n → GLEuclidean n)
    (hg : ∀ (s : ℝ) (k : Fin n),
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (g s ω) k) 2 (unitSphereMeasure n))
    (hBoundary : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      g R ω = (ω : GLEuclidean n))
    (k : Fin n) :
    vectorSphereRadialMean n g hg k R = 0 := by
  have hInt :
      (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (g R ω) k ∂(unitSphereMeasure n)) = 0 := by
    calc
      _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ((ω : GLEuclidean n) k) ∂(unitSphereMeasure n) := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hBoundary ω]
      _ = 0 := hOdd k
  have hMean :
      sphereMeanCoefficient n
        (scalarSphereFamilyTrace n
          (fun s y => (g s y) k) (fun s => hg s k) R) = 0 := by
    rw [sphereMeanCoefficient_eq_integral]
    have hTraceInt :
        (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          (scalarSphereFamilyTrace n
            (fun s y => (g s y) k) (fun s => hg s k) R) ω
              ∂(unitSphereMeasure n)) =
        ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          (g R ω) k ∂(unitSphereMeasure n) := by
      apply integral_congr_ae
      filter_upwards [(hg R k).coeFn_toLp] with ω hω
      exact hω
    rw [hTraceInt, hInt]
    ring
  unfold vectorSphereRadialMean scalarSphereRadialMean
  rw [hMean]
  ring

end

end BrezisOP6
