import BrezisOP6.SphereRadialL2FiniteBall
import BrezisOP6.SphereBoundaryMeanZero

/-!
# An honest finite-ball sphere family at every real radius

The quotient field itself is used at every interior positive radius.  At
the outer radius the family records the identity boundary trace; elsewhere
it is set to zero.  The values outside `(0,R)` are only a choice of `L²`
representatives for a radius-indexed family.  No smooth extension of the
quotient field beyond the ball is claimed or used.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set
open scoped Topology

/-- The finite-ball spherical family used in the energy comparison. -/
def finiteBallSphereFamily (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (s : ℝ) (y : GLEuclidean n) : GLEuclidean n :=
  if s ∈ Ioo (0 : ℝ) R then z (s • y)
  else if s = R then y else 0

theorem finiteBallSphereFamily_interior (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) R)
    (y : GLEuclidean n) :
    finiteBallSphereFamily n R z s y = z (s • y) := by
  simp [finiteBallSphereFamily, hs]

theorem finiteBallSphereFamily_outer (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (y : GLEuclidean n) :
    finiteBallSphereFamily n R z R y = y := by
  simp [finiteBallSphereFamily]

theorem finiteBallSphereFamily_zero (n : ℕ) (R : ℝ)
    (hR : 0 < R) (z : GLEuclidean n → GLEuclidean n)
    (y : GLEuclidean n) :
    finiteBallSphereFamily n R z 0 y = 0 := by
  simp [finiteBallSphereFamily, hR.ne]

/-- The concrete sphere trace of every target coordinate is in `L²` for
every real radius.  At interior radii this uses only punctured-ball `C¹`
regularity and compactness of the unit sphere. -/
theorem finiteBallSphereFamily_memLp (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (s : ℝ) (k : Fin n) :
    MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      (finiteBallSphereFamily n R z s ω) k) 2
      (unitSphereMeasure n) := by
  by_cases hs : s ∈ Ioo (0 : ℝ) R
  · have hRay : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          s • (ω : GLEuclidean n)) :=
      (continuous_const_smul s).comp continuous_subtype_val
    have hMaps : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
        s • (ω : GLEuclidean n) ∈
          {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} := by
      intro ω
      have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
        mem_sphere_zero_iff_norm.mp ω.property
      have hnorm : ‖s • (ω : GLEuclidean n)‖ = s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hω]
        ring
      change 0 < ‖s • (ω : GLEuclidean n)‖ ∧
        ‖s • (ω : GLEuclidean n)‖ < R
      rw [hnorm]
      exact hs
    have hCont : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          (finiteBallSphereFamily n R z s ω) k) := by
      have hZ : Continuous
          (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
            z (s • (ω : GLEuclidean n))) :=
        hz.continuousOn.comp_continuous hRay hMaps
      simpa only [finiteBallSphereFamily_interior n R z s hs] using
        (EuclideanSpace.proj k).continuous.comp hZ
    exact hCont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · by_cases hsR : s = R
    · subst s
      have hCont : Continuous
          (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
            (finiteBallSphereFamily n R z R ω) k) := by
        simpa only [finiteBallSphereFamily_outer] using
          (EuclideanSpace.proj k).continuous.comp continuous_subtype_val
      exact hCont.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · have hCont : Continuous
          (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
            (finiteBallSphereFamily n R z s ω) k) := by
        simpa [finiteBallSphereFamily, hs, hsR] using
          (continuous_const : Continuous
            (fun _ : Metric.sphere (0 : GLEuclidean n) 1 =>
              (0 : ℝ)))
      exact hCont.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- The interior radial derivative in the actual sphere's real `L²`
space, using the continuous Fréchet derivative of one target coordinate. -/
def finiteBallSphereFamilyRadialL2 (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (k : Fin n) : UnitSphereL2 n := by
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  exact finiteBallRayDerivativeL2 n R (fun x => (z x) k) hk r

/-- The actual finite-ball radial `L²` derivative varies continuously
with the interior radius. -/
theorem finiteBallSphereFamilyRadialL2_continuousOn (n : ℕ)
    (R : ℝ) (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n) :
    ContinuousOn (fun r => finiteBallSphereFamilyRadialL2 n R z hz r k)
      (Ioo (0 : ℝ) R) := by
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  exact finiteBallRayDerivativeL2_continuousOn n R
    (fun x => (z x) k) hk

/-- The explicitly extended family has the actual radial `L²` derivative
at each interior radius; outside that open interval no derivative is
asserted. -/
theorem finiteBallSphereFamily_hasDerivAt_interior (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) (k : Fin n) :
    HasDerivAt
      (scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k))
      (finiteBallSphereFamilyRadialL2 n R z hz r k) r := by
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  exact scalarSphereFamilyTrace_hasDerivAt_finiteBallDerivativeL2 n R
    (fun x => (z x) k) hk
    (fun s y => (finiteBallSphereFamily n R z s y) k)
    (fun s => finiteBallSphereFamily_memLp n R z hz s k)
    (by
      intro s hs ω
      simpa only [Function.comp_def,
        finiteBallSphereFamily_interior n R z s hs])
    r hr

/-- The pointwise radial derivative of the explicit family agrees with
the Fréchet radial derivative of the physical field at each interior
sphere. -/
theorem finiteBallSphereFamily_pointwise_ray_deriv (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) (k : Fin n) :
    deriv (fun s : ℝ =>
      (finiteBallSphereFamily n R z s ω) k) r =
      (fderiv ℝ (fun x : GLEuclidean n => (z x) k)
        (r • (ω : GLEuclidean n)))
        (ω : GLEuclidean n) := by
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  have hx : r • (ω : GLEuclidean n) ∈
      {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    have hnorm : ‖r • (ω : GLEuclidean n)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
      ring
    change 0 < ‖r • (ω : GLEuclidean n)‖ ∧
      ‖r • (ω : GLEuclidean n)‖ < R
    rw [hnorm]
    exact hr
  have hopen : IsOpen
      {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hf : HasFDerivAt (fun x : GLEuclidean n => (z x) k)
      (fderiv ℝ (fun x : GLEuclidean n => (z x) k)
        (r • (ω : GLEuclidean n)))
      (r • (ω : GLEuclidean n)) :=
    ((hk.differentiableOn_one).differentiableAt
      (hopen.mem_nhds hx)).hasFDerivAt
  have hray : HasDerivAt
      (fun s : ℝ => s • (ω : GLEuclidean n))
      (ω : GLEuclidean n) r := by
    simpa using (hasDerivAt_id r).smul_const (ω : GLEuclidean n)
  have hactual := hf.comp_hasDerivAt r hray
  have hnear :
      (fun s : ℝ => (finiteBallSphereFamily n R z s ω) k) =ᶠ[𝓝 r]
        (fun s : ℝ => (z (s • (ω : GLEuclidean n))) k) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    rw [finiteBallSphereFamily_interior n R z s hs]
  exact (hactual.congr_of_eventuallyEq hnear).deriv

/-- The radial `L²` derivative used in the bridge has the actual
pointwise ray derivative as its almost-everywhere representative. -/
theorem finiteBallSphereFamilyRadialL2_ae_eq_ray_deriv (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) (k : Fin n) :
    finiteBallSphereFamilyRadialL2 n R z hz r k =ᶠ[ae (unitSphereMeasure n)]
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        deriv (fun s : ℝ =>
          (finiteBallSphereFamily n R z s ω) k) r) := by
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  have hrep := finiteBallRayDerivativeL2_ae_eq n R
    (fun x => (z x) k) hk r hr
  filter_upwards [hrep] with ω hω
  exact hω.trans
    (finiteBallSphereFamily_pointwise_ray_deriv n R z hz r hr ω k).symm

/-- No radial-square integrability hypothesis is needed at a fixed
interior sphere: local `C¹` regularity supplies it. -/
theorem finiteBallSphereFamily_rayDeriv_sq_integrable (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) (k : Fin n) :
    Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (deriv (fun s : ℝ =>
          (finiteBallSphereFamily n R z s ω) k) r) ^ 2)
      (unitSphereMeasure n) := by
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  have hInt := finiteBallRayDerivative_sq_integrable n R
    (fun x => (z x) k) hk r hr
  convert hInt using 1
  ext ω
  rw [finiteBallSphereFamily_pointwise_ray_deriv n R z hz r hr ω k]

end

end BrezisOP6
