import BrezisOP6.SphereUniformToL2

/-!
# Uniform scaled traces give the regularized mean's right limit

The radius-zero value of the totalized sphere family is irrelevant.  The
right trace is determined by the uniformly convergent scaled family on
positive spheres, and finite sphere measure upgrades this to `L²`.
-/

namespace BrezisOP6

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem scalarSphereRadialMean_tendsto_of_uniform_scaled
    (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => g r ω) 2
          (unitSphereMeasure n))
    (g₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hg₀ : MemLp g₀ 2 (unitSphereMeasure n))
    (huniform : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ‖r • g r ω - g₀ ω‖ < ε) :
    Tendsto (scalarSphereRadialMean n g hg)
      (𝓝[>] (0 : ℝ))
      (𝓝 (sphereMeanCoefficient n (hg₀.toLp g₀))) := by
  have hscaledMem (r : ℝ) :
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => r • g r ω)
        2 (unitSphereMeasure n) :=
    (hg r).const_smul r
  have hLp := tendsto_L2_of_uniform_pointwise
    (unitSphereMeasure n)
    (fun r ω => r • g r ω) g₀ hscaledMem hg₀ huniform
  have hTraceEq (r : ℝ) :
      r • scalarSphereFamilyTrace n g hg r =
      (hscaledMem r).toLp
        (fun ω : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1 => r • g r ω) := by
    simpa only [scalarSphereFamilyTrace, unitSphereTrace] using
      ((hg r).toLp_const_smul r).symm
  apply scalarSphereRadialMean_tendsto_of_scaled_trace
    n g hg (hg₀.toLp g₀)
  simpa only [hTraceEq] using hLp

theorem vectorSphereRadialMean_tendsto_of_uniform_scaled
    (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ (r : ℝ) (i : Fin n),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => (g r ω) i) 2
          (unitSphereMeasure n))
    (i : Fin n)
    (g₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hg₀ : MemLp g₀ 2 (unitSphereMeasure n))
    (huniform : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ‖r • (g r ω) i - g₀ ω‖ < ε) :
    Tendsto (vectorSphereRadialMean n g hg i)
      (𝓝[>] (0 : ℝ))
      (𝓝 (sphereMeanCoefficient n (hg₀.toLp g₀))) :=
  scalarSphereRadialMean_tendsto_of_uniform_scaled
    n (fun r x => (g r x) i) (fun r => hg r i)
      g₀ hg₀ huniform

end

end BrezisOP6
