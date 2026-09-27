import BrezisOP6.SphereTraceGradient
import BrezisOP6.SphereBridgeIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Radial differentiability of smooth spherical traces in `L²`

The analytic mechanism is to first differentiate the ray family in the
sup-norm space of continuous functions on the compact sphere.  Pointwise
ray differentiation and continuity of the continuous-function-valued
derivative suffice by the fundamental theorem of calculus.  The canonical
continuous linear map from continuous functions to `L²` then transfers
the derivative.  This avoids assuming radial `L²` differentiability.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

private theorem continuousMap_hasDerivAt_of_pointwise
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (F D : ℝ → C(α, ℝ)) (hD : Continuous D)
    (hpoint : ∀ (t : ℝ) (ω : α),
      HasDerivAt (fun s : ℝ => F s ω) (D t ω) t)
    (r : ℝ) : HasDerivAt F (D r) r := by
  have hint (s : ℝ) : IntervalIntegrable D volume r s :=
    hD.intervalIntegrable r s
  have hFTCeq (s : ℝ) :
      (∫ t in r..s, D t) = F s - F r := by
    ext ω
    have hevalCont : Continuous (fun t : ℝ => D t ω) :=
      (ContinuousMap.evalCLM ℝ ω).continuous.comp hD
    have hpointInt :
        (∫ t in r..s, D t ω) = F s ω - F r ω :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hpoint t ω)
        (hevalCont.intervalIntegrable r s)
    calc
      (∫ t in r..s, D t) ω =
          ∫ t in r..s, D t ω := by
            simpa only [ContinuousMap.evalCLM_apply] using
              ((ContinuousMap.evalCLM ℝ ω).intervalIntegral_comp_comm
                (hint s)).symm
      _ = F s ω - F r ω := hpointInt
      _ = (F s - F r) ω := rfl
  have hFTC :
      HasDerivAt (fun s : ℝ => ∫ t in r..s, D t)
        (D r) r :=
    intervalIntegral.integral_hasDerivAt_right
      (hint r)
      hD.aestronglyMeasurable.stronglyMeasurableAtFilter
      hD.continuousAt
  have heq :
      (fun s : ℝ => ∫ t in r..s, D t) =
        (fun s : ℝ => F s - F r) :=
    funext hFTCeq
  rw [heq] at hFTC
  simpa only [sub_add_cancel] using hFTC.add_const (F r)

/-- Continuous scalar spherical trace of an ambient `C¹` field. -/
def scalarSphereRayContinuous (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) :=
  ⟨fun ω => g (r • (ω : GLEuclidean n)),
    hg.continuous.comp
      ((continuous_const_smul r).comp continuous_subtype_val)⟩

/-- Continuous radial-derivative representative on the unit sphere. -/
def scalarSphereRayDerivativeContinuous (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) := by
  have hRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        r • (ω : GLEuclidean n)) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have hF : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        fderiv ℝ g (r • (ω : GLEuclidean n))) :=
    (hg.continuous_fderiv one_ne_zero).comp hRay
  exact ⟨fun ω => (fderiv ℝ g (r • (ω : GLEuclidean n)))
      (ω : GLEuclidean n), hF.clm_apply continuous_subtype_val⟩

/-- The derivative representative varies continuously in the sup norm.
This is where compactness of the sphere supplies uniformity in `ω`. -/
theorem scalarSphereRayDerivativeContinuous_continuous (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g) :
    Continuous (scalarSphereRayDerivativeContinuous n g hg) := by
  have hRay : Continuous
      (fun p : ℝ × Metric.sphere (0 : GLEuclidean n) 1 =>
        p.1 • (p.2 : GLEuclidean n)) :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  have hF : Continuous
      (fun p : ℝ × Metric.sphere (0 : GLEuclidean n) 1 =>
        fderiv ℝ g (p.1 • (p.2 : GLEuclidean n))) :=
    (hg.continuous_fderiv one_ne_zero).comp hRay
  have hDunc : Continuous
      (fun p : ℝ × Metric.sphere (0 : GLEuclidean n) 1 =>
        (fderiv ℝ g (p.1 • (p.2 : GLEuclidean n)))
          (p.2 : GLEuclidean n)) :=
    hF.clm_apply (continuous_subtype_val.comp continuous_snd)
  exact ContinuousMap.continuous_of_continuous_uncurry _ hDunc

/-- A `C¹` ambient scalar field yields a genuinely differentiable path
of continuous spherical traces, with its derivative computed from the
ambient Fréchet derivative along rays. -/
theorem scalarSphereRayContinuous_hasDerivAt (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) :
    HasDerivAt (scalarSphereRayContinuous n g hg)
      (scalarSphereRayDerivativeContinuous n g hg r) r := by
  apply continuousMap_hasDerivAt_of_pointwise
    (scalarSphereRayContinuous n g hg)
    (scalarSphereRayDerivativeContinuous n g hg)
    (scalarSphereRayDerivativeContinuous_continuous n g hg)
  intro t ω
  have hray : HasDerivAt
      (fun s : ℝ => s • (ω : GLEuclidean n))
      (ω : GLEuclidean n) t := by
    simpa using (hasDerivAt_id t).smul_const (ω : GLEuclidean n)
  have hf : HasFDerivAt g (fderiv ℝ g (t • (ω : GLEuclidean n)))
      (t • (ω : GLEuclidean n)) :=
    (hg.differentiable_one (t • (ω : GLEuclidean n))).hasFDerivAt
  have hcomp := hf.comp_hasDerivAt t hray
  simpa only [scalarSphereRayContinuous,
    scalarSphereRayDerivativeContinuous] using hcomp

/-- The canonical `L²` spherical trace of the ambient `C¹` scalar field.
The representative is the actual function `ω ↦ g(rω)`. -/
def scalarSphereRayL2 (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) : UnitSphereL2 n :=
  (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
    (scalarSphereRayContinuous n g hg r)

/-- The canonical `L²` spherical trace is differentiable, with the
derivative represented by the actual radial Fréchet derivative on the
sphere. -/
theorem scalarSphereRayL2_hasDerivAt (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) :
    HasDerivAt (scalarSphereRayL2 n g hg)
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayDerivativeContinuous n g hg r)) r := by
  let T : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) →L[ℝ]
      UnitSphereL2 n := ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ
  have hT : HasFDerivAt T T (scalarSphereRayContinuous n g hg r) :=
    T.hasFDerivAt
  simpa only [scalarSphereRayL2, T] using
    hT.comp_hasDerivAt r (scalarSphereRayContinuous_hasDerivAt n g hg r)

/-- The actual continuous ray trace is in `L²` on the compact unit sphere. -/
def scalarSphereRayMemLp (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) :
    MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      g (r • (ω : GLEuclidean n))) 2 (unitSphereMeasure n) := by
  have hcont : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        g (r • (ω : GLEuclidean n))) :=
    (scalarSphereRayContinuous n g hg r).continuous
  exact hcont.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The canonical `ContinuousMap.toLp` trace agrees with the existing
`MemLp.toLp` trace used in the spherical bridge. -/
theorem scalarSphereRayL2_eq_familyTrace (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) :
    scalarSphereRayL2 n g hg r =
      scalarSphereFamilyTrace n
        (fun s x => g (s • x))
        (scalarSphereRayMemLp n g hg) r := by
  apply Lp.ext
  have hc := ContinuousMap.coeFn_toLp
    (p := 2) (μ := unitSphereMeasure n) (𝕜 := ℝ)
    (scalarSphereRayContinuous n g hg r)
  have hm := (scalarSphereRayMemLp n g hg r).coeFn_toLp
  exact hc.trans hm.symm

/-- The existing scalar bridge trace, for the actual ray family of a
`C¹` ambient field, is differentiable in its `L²` norm.  Its derivative
is the concrete `L²` class of `ω ↦ Dg(rω)ω`. -/
theorem scalarSphereFamilyTrace_ray_hasDerivAt (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g)
    (r : ℝ) :
    HasDerivAt
      (scalarSphereFamilyTrace n
        (fun s x => g (s • x))
        (scalarSphereRayMemLp n g hg))
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayDerivativeContinuous n g hg r)) r := by
  have heq :
      (scalarSphereFamilyTrace n
        (fun s x => g (s • x))
        (scalarSphereRayMemLp n g hg)) =
      scalarSphereRayL2 n g hg := by
    funext s
    exact (scalarSphereRayL2_eq_familyTrace n g hg s).symm
  rw [heq]
  exact scalarSphereRayL2_hasDerivAt n g hg r

/-- Target-coordinate version directly matching the vector spherical
bridge's radial `L²` derivative input. -/
theorem vectorSphereFamilyTrace_ray_hasDerivAt (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (hz : ContDiff ℝ 1 z)
    (k : Fin n) (r : ℝ) :
    let g : GLEuclidean n → ℝ := fun x => (z x) k
    let hg : ContDiff ℝ 1 g := by
      simpa only [g, EuclideanSpace.coe_proj, Function.comp_def] using
        (EuclideanSpace.proj k).contDiff.comp hz
    HasDerivAt
      (scalarSphereFamilyTrace n
        (fun s x => g (s • x))
        (scalarSphereRayMemLp n g hg))
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayDerivativeContinuous n g hg r)) r := by
  exact scalarSphereFamilyTrace_ray_hasDerivAt n
    (fun x : GLEuclidean n => (z x) k)
    (by
      simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
        (EuclideanSpace.proj k).contDiff.comp hz) r

end

end BrezisOP6
