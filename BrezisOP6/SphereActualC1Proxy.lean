import BrezisOP6.SphereSmoothMeanC1
import BrezisOP6.EnergyActualScaledSphereUniform
import BrezisOP6.BridgeFluxC1Proxy

/-!
# Removable C¹ zero mode for a smooth finite-ball competitor

The actual radial mean is totalized at zero. For positive radii it is
the smooth spherical mean of the numerator divided by the regular radial
factor H(r²). This gives the local representative used to integrate the
origin flux.
-/

namespace BrezisOP6

open Filter MeasureTheory Set Metric
open scoped Topology

noncomputable section

theorem regular_factor_nonzero_on_small_radii
    (H : ℝ → ℝ) (hH : ContDiff ℝ 1 H) (hH0 : H 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ r ∈ Ioo (-δ) δ, H (r ^ 2) ≠ 0 := by
  have hcomp : ContinuousAt (fun r : ℝ => H (r ^ 2)) 0 := by
    have hsq : ContinuousAt (fun r : ℝ => r ^ 2) 0 := by fun_prop
    simpa only [Function.comp_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using hH.continuous.continuousAt.comp hsq
  have hne : ∀ᶠ r in 𝓝 (0 : ℝ), H (r ^ 2) ≠ 0 :=
    hcomp.eventually (eventually_ne_nhds (by simpa using hH0))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hne
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact abs_lt.mpr hr

def regularizedNumeratorSphereMean (n : ℕ)
    (H : ℝ → ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u) (k : Fin n) (r : ℝ) : ℝ :=
  (H (r ^ 2))⁻¹ * smoothSphereCoordinateMean n u hu k r

theorem regularizedNumeratorSphereMean_contDiffOn
    (n : ℕ) (H : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hH : ContDiff ℝ 1 H) (hu : ContDiff ℝ 1 u)
    (k : Fin n) (δ : ℝ)
    (hHne : ∀ r ∈ Ioo (-δ) δ, H (r ^ 2) ≠ 0) :
    ContDiffOn ℝ 1
      (regularizedNumeratorSphereMean n H u hu k)
      (Ioo (-δ) δ) := by
  unfold regularizedNumeratorSphereMean
  have hcomp : ContDiff ℝ 1 (fun r : ℝ => H (r ^ 2)) := by
    fun_prop
  exact (hcomp.contDiffOn.inv hHne).mul
    (smoothSphereCoordinateMean_contDiff n u hu k).contDiffOn

theorem regularizedNumeratorSphereMean_contDiffOn_nonzero_set
    (n : ℕ) (H : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hH : ContDiff ℝ 1 H) (hu : ContDiff ℝ 1 u)
    (k : Fin n) :
    ContDiffOn ℝ 1
      (regularizedNumeratorSphereMean n H u hu k)
      {r : ℝ | H (r ^ 2) ≠ 0} := by
  unfold regularizedNumeratorSphereMean
  have hcomp : ContDiff ℝ 1 (fun r : ℝ => H (r ^ 2)) := by
    fun_prop
  exact (hcomp.contDiffOn.inv (fun r hr => hr)).mul
    (smoothSphereCoordinateMean_contDiff n u hu k).contDiffOn

/-- At a positive radius, the regularized numerator mean is exactly
the actual rescaled quotient mean. -/
theorem actual_finiteBallSphereRadialMean_eq_regularizedNumeratorMean
    (n : ℕ) (R : ℝ) (f H : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u)
    (hf : ∀ s, 0 < s → s ≤ R → f s = s * H (s ^ 2))
    (hfpos : ∀ s, 0 < s → s ≤ R → 0 < f s)
    (hz : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (f ‖x‖)⁻¹ • u x)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n) (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    vectorSphereRadialMean n
      (finiteBallSphereFamily n R
        (fun x => (f ‖x‖)⁻¹ • u x))
      (fun s i => finiteBallSphereFamily_memLp n R
        (fun x => (f ‖x‖)⁻¹ • u x) hz s i) k r =
      regularizedNumeratorSphereMean n H u hu k r := by
  let z : GLEuclidean n → GLEuclidean n :=
    fun x => (f ‖x‖)⁻¹ • u x
  let g : GLEuclidean n → ℝ := fun x => (u x) k
  have hg : ContDiff ℝ 1 g := by
    simpa only [g, EuclideanSpace.coe_proj, Function.comp_def]
      using (EuclideanSpace.proj k).contDiff.comp hu
  let actual : UnitSphereL2 n :=
    scalarSphereFamilyTrace n
      (fun s y => (finiteBallSphereFamily n R z s y) k)
      (fun s => finiteBallSphereFamily_memLp n R z hz s k) r
  let smooth : UnitSphereL2 n := scalarSphereRayL2 n g hg r
  let a : ℝ := (H (r ^ 2))⁻¹
  have hLp : r • actual = a • smooth := by
    apply Lp.ext
    have hactual := (finiteBallSphereFamily_memLp n R z hz r k).coeFn_toLp
    have hsmooth := ContinuousMap.coeFn_toLp
      (p := 2) (μ := unitSphereMeasure n) (𝕜 := ℝ)
      (scalarSphereRayContinuous n g hg r)
    filter_upwards [Lp.coeFn_smul r actual,
      Lp.coeFn_smul a smooth, hactual, hsmooth] with
      ω hscaleActual hscaleSmooth hactualPoint hsmoothPoint
    have hpoint : r • (finiteBallSphereFamily n R z r ω) =
        a • u (energySphereRay n ω r) := by
      rw [finiteBallSphereFamily_interior n R z r ⟨hr, hrR⟩]
      simpa only [z, a, energySphereRay] using
        rescaled_radialQuotient_ray_eq_factor
          n R f H u r hr hrR.le hf hfpos ω
    have hcoord : r • (finiteBallSphereFamily n R z r ω) k =
        a • (u (energySphereRay n ω r)) k := by
      simpa only [Pi.smul_apply] using congrArg
        (fun y : GLEuclidean n => y k) hpoint
    change (r • actual) ω = (a • smooth) ω
    rw [hscaleActual, hscaleSmooth]
    simp only [Pi.smul_apply]
    have haeq : actual ω = (finiteBallSphereFamily n R z r ω) k :=
      hactualPoint
    have hseq : smooth ω = (u (energySphereRay n ω r)) k := by
      simpa only [g, scalarSphereRayContinuous, energySphereRay]
        using hsmoothPoint
    rw [haeq, hseq]
    exact hcoord
  change r * sphereMeanCoefficient n actual =
    a * sphereMeanCoefficient n smooth
  calc
    r * sphereMeanCoefficient n actual =
        sphereMeanCoefficient n (r • actual) := by
          simp only [sphereMeanCoefficient, real_inner_smul_left]
    _ = sphereMeanCoefficient n (a • smooth) := by rw [hLp]
    _ = a * sphereMeanCoefficient n smooth := by
          simp only [sphereMeanCoefficient, real_inner_smul_left]

end

end BrezisOP6
