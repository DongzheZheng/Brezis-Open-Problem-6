import BrezisOP6.SphereBridgeIntegral

/-!
# One-sided limits of the regularized spherical mean

The sphere family used for the quotient is totalized to zero at radius
zero.  Its regularized mean `b(r)=r·mean(z(rω))` can nevertheless converge
to a nonzero value as `r↓0`.  This module transfers convergence of the
scaled `L²` sphere trace to the mean coefficient.  The smooth-competitor
identity `r z(rω)=u(rω)/H_f(r²)` supplies the scaled-trace convergence.
-/

namespace BrezisOP6

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem scalarSphereRadialMean_tendsto_of_scaled_trace
    (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => g r ω) 2
          (unitSphereMeasure n))
    (v : UnitSphereL2 n)
    (hscaled : Tendsto
      (fun r : ℝ => r • scalarSphereFamilyTrace n g hg r)
      (𝓝[>] (0 : ℝ)) (𝓝 v)) :
    Tendsto (scalarSphereRadialMean n g hg)
      (𝓝[>] (0 : ℝ)) (𝓝 (sphereMeanCoefficient n v)) := by
  have hMeanContinuous : Continuous (sphereMeanCoefficient n) := by
    unfold sphereMeanCoefficient
    fun_prop
  have hMeanLimit := (hMeanContinuous.tendsto v).comp hscaled
  have hEq : scalarSphereRadialMean n g hg =
      fun r => sphereMeanCoefficient n
        (r • scalarSphereFamilyTrace n g hg r) := by
    funext r
    simp [scalarSphereRadialMean, sphereMeanCoefficient,
      real_inner_smul_left]
  simpa only [hEq] using hMeanLimit

theorem vectorSphereRadialMean_tendsto_of_scaled_trace
    (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ (r : ℝ) (i : Fin n),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => (g r ω) i) 2
          (unitSphereMeasure n))
    (i : Fin n) (v : UnitSphereL2 n)
    (hscaled : Tendsto
      (fun r : ℝ => r • scalarSphereFamilyTrace n
        (fun s y => (g s y) i) (fun s => hg s i) r)
      (𝓝[>] (0 : ℝ)) (𝓝 v)) :
    Tendsto (vectorSphereRadialMean n g hg i)
      (𝓝[>] (0 : ℝ)) (𝓝 (sphereMeanCoefficient n v)) :=
  scalarSphereRadialMean_tendsto_of_scaled_trace
    n (fun s y => (g s y) i) (fun s => hg s i) v hscaled

end

end BrezisOP6
