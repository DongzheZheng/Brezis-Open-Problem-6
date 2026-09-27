import BrezisOP6.SpherePuncturedAngular

/-!
# The concrete square norm of a spherical `L²` trace

This module identifies Hilbert norms used in the bridge with ordinary
surface integrals of squares.  It is the measure-theoretic step needed to
compare the bridge with spatial gradient energy.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

/-- A real spherical `L²` norm is its actual squared surface integral. -/
theorem unitSphereL2_norm_sq_eq_integral (n : ℕ)
    (v : UnitSphereL2 n) :
    ‖v‖ ^ 2 =
      ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (v ω) ^ 2 ∂(unitSphereMeasure n) := by
  calc
    ‖v‖ ^ 2 = inner ℝ v v :=
      (real_inner_self_eq_norm_sq v).symm
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (v ω) ^ 2 ∂(unitSphereMeasure n) := by
      simp only [L2.inner_def, real_inner_self_eq_norm_sq,
        Real.norm_eq_abs, sq_abs]

/-- A trace built from a specified `MemLp` representative has exactly the
surface integral of its pointwise square as squared norm. -/
theorem unitSphereTrace_norm_sq_eq_integral (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      g ω) 2 (unitSphereMeasure n)) :
    ‖unitSphereTrace n g hg‖ ^ 2 =
      ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (g ω) ^ 2 ∂(unitSphereMeasure n) := by
  rw [unitSphereL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with ω hω
  simpa only [unitSphereTrace] using congrArg (fun x : ℝ => x ^ 2) hω

/-- The continuous-function embedding into real sphere `L²` has the
corresponding norm formula for a pointwise continuous field. -/
theorem continuousSphereTrace_norm_sq_eq_integral (n : ℕ)
    (g : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ)) :
    ‖(ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ) g‖ ^ 2 =
      ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (g ω) ^ 2 ∂(unitSphereMeasure n) := by
  rw [unitSphereL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp
    (p := 2) (μ := unitSphereMeasure n) (𝕜 := ℝ) g] with ω hω
  simpa using congrArg (fun x : ℝ => x ^ 2) hω

end

end BrezisOP6
