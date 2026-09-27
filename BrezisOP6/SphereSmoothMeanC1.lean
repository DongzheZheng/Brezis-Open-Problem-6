import BrezisOP6.SphereRadialL2Differentiability

/-!
# A smooth field has a C¹ radial spherical mean

The C¹ dependence of the spherical mean is obtained through the proved
continuous-function and L² ray derivatives, with no differentiation under
an unverified integral.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

def smoothSphereCoordinateMean (n : ℕ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u) (k : Fin n) (r : ℝ) : ℝ :=
  sphereMeanCoefficient n
    (scalarSphereRayL2 n
      (fun x : GLEuclidean n => (u x) k)
      (by
        simpa only [EuclideanSpace.coe_proj, Function.comp_def]
          using (EuclideanSpace.proj k).contDiff.comp hu) r)

theorem smoothSphereCoordinateMean_contDiff
    (n : ℕ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u) (k : Fin n) :
    ContDiff ℝ 1 (smoothSphereCoordinateMean n u hu k) := by
  let g : GLEuclidean n → ℝ := fun x => (u x) k
  have hg : ContDiff ℝ 1 g := by
    simpa only [g, EuclideanSpace.coe_proj, Function.comp_def]
      using (EuclideanSpace.proj k).contDiff.comp hu
  let D : ℝ → ℝ := fun r =>
    sphereMeanCoefficient n
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayDerivativeContinuous n g hg r))
  have hD : Continuous D := by
    have hmean : Continuous (sphereMeanCoefficient n) := by
      unfold sphereMeanCoefficient
      fun_prop
    exact hmean.comp
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ).continuous.comp
        (scalarSphereRayDerivativeContinuous_continuous n g hg))
  have hhas (r : ℝ) :
      HasDerivAt (smoothSphereCoordinateMean n u hu k) (D r) r := by
    simpa only [smoothSphereCoordinateMean, D, g, hg] using
      sphereMeanCoefficient_hasDerivAt n
        (scalarSphereRayL2 n g hg) r
        ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
          (scalarSphereRayDerivativeContinuous n g hg r))
        (scalarSphereRayL2_hasDerivAt n g hg r)
  apply (contDiff_one_iff_deriv).2
  refine ⟨fun r => (hhas r).differentiableAt, ?_⟩
  have hderiv : deriv (smoothSphereCoordinateMean n u hu k) = D := by
    funext r
    exact (hhas r).deriv
  rw [hderiv]
  exact hD

end

end BrezisOP6
