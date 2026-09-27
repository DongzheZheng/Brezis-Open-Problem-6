import BrezisOP6.SphereRadialL2Punctured

/-! Radial `L²` differentiation on a punctured finite ball. -/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set
open scoped Topology

private theorem continuousMap_hasDerivAt_of_pointwise_ball
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (F D : ℝ → C(α, ℝ)) (R : ℝ)
    (hD : ContinuousOn D (Ioo (0 : ℝ) R))
    (hpoint : ∀ t ∈ Ioo (0 : ℝ) R, ∀ ω : α,
      HasDerivAt (fun s : ℝ => F s ω) (D t ω) t)
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt F (D r) r := by
  have hseg (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) R) :
      uIcc r s ⊆ Ioo (0 : ℝ) R := by
    intro t ht
    rcases le_total r s with hrs | hsr
    · rw [uIcc_of_le hrs] at ht
      exact ⟨lt_of_lt_of_le hr.1 ht.1, lt_of_le_of_lt ht.2 hs.2⟩
    · rw [uIcc_of_ge hsr] at ht
      exact ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 hr.2⟩
  have hint (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) R) :
      IntervalIntegrable D volume r s :=
    ContinuousOn.intervalIntegrable (hD.mono (hseg s hs))
  have hFTCeq (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) R) :
      (∫ t in r..s, D t) = F s - F r := by
    ext ω
    have hevalCont : ContinuousOn (fun t : ℝ => D t ω) (Ioo (0 : ℝ) R) :=
      (ContinuousMap.evalCLM ℝ ω).continuous.comp_continuousOn' hD
    have hpointInt :
        (∫ t in r..s, D t ω) = F s ω - F r ω := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        exact hpoint t (hseg s hs ht) ω
      · exact (hevalCont.mono (hseg s hs)).intervalIntegrable
    calc
      (∫ t in r..s, D t) ω =
          ∫ t in r..s, D t ω := by
            simpa only [ContinuousMap.evalCLM_apply] using
              ((ContinuousMap.evalCLM ℝ ω).intervalIntegral_comp_comm
                (hint s hs)).symm
      _ = F s ω - F r ω := hpointInt
      _ = (F s - F r) ω := rfl
  have hDAt : ContinuousAt D r :=
    hD.continuousAt (isOpen_Ioo.mem_nhds hr)
  have hDMeas : StronglyMeasurableAtFilter D (𝓝 r) volume :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hD) r hr
  have hFTC : HasDerivAt (fun s : ℝ => ∫ t in r..s, D t) (D r) r :=
    intervalIntegral.integral_hasDerivAt_right (hint r hr) hDMeas hDAt
  have heq :
      (fun s : ℝ => ∫ t in r..s, D t) =ᶠ[𝓝 r]
        (fun s : ℝ => F s - F r) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact hFTCeq s hs
  have hdiff : HasDerivAt (fun s : ℝ => F s - F r) (D r) r :=
    hFTC.congr_of_eventuallyEq heq.symm
  simpa only [sub_add_cancel] using hdiff.add_const (F r)

private theorem sphereRay_mem_puncturedBall (n : ℕ) (R s : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (hs : s ∈ Ioo (0 : ℝ) R) :
    0 < ‖s • (ω : GLEuclidean n)‖ ∧
      ‖s • (ω : GLEuclidean n)‖ < R := by
  have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hω] using hs

private def finiteBallRayContinuous (n : ℕ) (R : ℝ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (s : ℝ) : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) := by
  by_cases hs : s ∈ Ioo (0 : ℝ) R
  · have hRay : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          s • (ω : GLEuclidean n)) :=
      (continuous_const_smul s).comp continuous_subtype_val
    exact ⟨fun ω => g (s • (ω : GLEuclidean n)),
      hg.continuousOn.comp_continuous hRay
        (fun ω => sphereRay_mem_puncturedBall n R s ω hs)⟩
  · exact 0

private def finiteBallRayDerivativeContinuous (n : ℕ) (R : ℝ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (s : ℝ) : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) := by
  by_cases hs : s ∈ Ioo (0 : ℝ) R
  · have hRay : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          s • (ω : GLEuclidean n)) :=
      (continuous_const_smul s).comp continuous_subtype_val
    have hopen : IsOpen {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hF : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          fderiv ℝ g (s • (ω : GLEuclidean n))) :=
      (hg.continuousOn_fderiv_of_isOpen hopen (by norm_num)).comp_continuous
        hRay (fun ω => sphereRay_mem_puncturedBall n R s ω hs)
    exact ⟨fun ω => (fderiv ℝ g (s • (ω : GLEuclidean n)))
      (ω : GLEuclidean n), hF.clm_apply continuous_subtype_val⟩
  · exact 0

/-- The concrete `L²` representative of the radial ray derivative at a
finite-ball radius.  Its pointwise continuous representative is the
Fréchet derivative applied to the unit direction. -/
def finiteBallRayDerivativeL2 (n : ℕ) (R : ℝ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) : UnitSphereL2 n :=
  (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
    (finiteBallRayDerivativeContinuous n R g hg r)

/-- The named `L²` derivative is represented almost everywhere by the
actual directional Fréchet derivative along the sphere's radial vector. -/
theorem finiteBallRayDerivativeL2_ae_eq (n : ℕ) (R : ℝ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    finiteBallRayDerivativeL2 n R g hg r =ᶠ[ae (unitSphereMeasure n)]
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (fderiv ℝ g (r • (ω : GLEuclidean n)))
          (ω : GLEuclidean n)) := by
  simpa [finiteBallRayDerivativeL2,
    finiteBallRayDerivativeContinuous, hr] using
    (ContinuousMap.coeFn_toLp (p := 2)
      (μ := unitSphereMeasure n) (𝕜 := ℝ)
      (finiteBallRayDerivativeContinuous n R g hg r))

/-- The actual radial directional derivative has an integrable square
on each interior sphere, directly from local `C¹` regularity and sphere
compactness. -/
theorem finiteBallRayDerivative_sq_integrable (n : ℕ) (R : ℝ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        ((fderiv ℝ g (r • (ω : GLEuclidean n)))
          (ω : GLEuclidean n)) ^ 2)
      (unitSphereMeasure n) := by
  have hRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        r • (ω : GLEuclidean n)) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have hF : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        fderiv ℝ g (r • (ω : GLEuclidean n))) := by
    have hopen : IsOpen {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    exact (hg.continuousOn_fderiv_of_isOpen hopen
      (by norm_num)).comp_continuous hRay
        (fun ω => sphereRay_mem_puncturedBall n R r ω hr)
  have hD : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (fderiv ℝ g (r • (ω : GLEuclidean n)))
          (ω : GLEuclidean n)) :=
    hF.clm_apply continuous_subtype_val
  exact (hD.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem finiteBallRayDerivativeContinuous_continuousOn (n : ℕ)
    (R : ℝ) (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R}) :
    ContinuousOn (finiteBallRayDerivativeContinuous n R g hg)
      (Ioo (0 : ℝ) R) := by
  let S := Metric.sphere (0 : GLEuclidean n) 1
  let U : Set (ℝ × S) := Ioo (0 : ℝ) R ×ˢ univ
  have hRay : Continuous (fun p : ℝ × S =>
      p.1 • (p.2 : GLEuclidean n)) :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  have hRayMaps : MapsTo
      (fun p : ℝ × S => p.1 • (p.2 : GLEuclidean n))
      U {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    intro p hp
    exact sphereRay_mem_puncturedBall n R p.1 p.2 hp.1
  have hopen : IsOpen {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hF : ContinuousOn (fun p : ℝ × S =>
      fderiv ℝ g (p.1 • (p.2 : GLEuclidean n))) U :=
    (hg.continuousOn_fderiv_of_isOpen hopen
      (by norm_num)).comp hRay.continuousOn hRayMaps
  have hDunc : ContinuousOn (fun p : ℝ × S =>
      (fderiv ℝ g (p.1 • (p.2 : GLEuclidean n)))
        (p.2 : GLEuclidean n)) U :=
    hF.clm_apply (continuous_subtype_val.comp continuous_snd).continuousOn
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  apply hDunc.congr
  intro p hp
  change (finiteBallRayDerivativeContinuous n R g hg p.1) p.2 = _
  simp [finiteBallRayDerivativeContinuous, hp.1]

/-- The concrete radial derivative has a continuous `L²` representative
on every punctured finite-ball radius interval. -/
theorem finiteBallRayDerivativeL2_continuousOn (n : ℕ)
    (R : ℝ) (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R}) :
    ContinuousOn (finiteBallRayDerivativeL2 n R g hg)
      (Ioo (0 : ℝ) R) := by
  exact (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ).continuous.comp_continuousOn
    (finiteBallRayDerivativeContinuous_continuousOn n R g hg)

private theorem finiteBallRayContinuous_hasDerivAt (n : ℕ)
    (R : ℝ) (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt (finiteBallRayContinuous n R g hg)
      (finiteBallRayDerivativeContinuous n R g hg r) r := by
  refine continuousMap_hasDerivAt_of_pointwise_ball
    (finiteBallRayContinuous n R g hg)
    (finiteBallRayDerivativeContinuous n R g hg) R
    (finiteBallRayDerivativeContinuous_continuousOn n R g hg)
    ?_ r hr
  intro t ht ω
  have hray : HasDerivAt
      (fun s : ℝ => s • (ω : GLEuclidean n))
      (ω : GLEuclidean n) t := by
    simpa using (hasDerivAt_id t).smul_const (ω : GLEuclidean n)
  have hx : t • (ω : GLEuclidean n) ∈
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    sphereRay_mem_puncturedBall n R t ω ht
  have hopen : IsOpen {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hf : HasFDerivAt g (fderiv ℝ g (t • (ω : GLEuclidean n)))
      (t • (ω : GLEuclidean n)) :=
    (hg.differentiableOn_one).differentiableAt (hopen.mem_nhds hx) |>.hasFDerivAt
  have hcomp := hf.comp_hasDerivAt t hray
  have hnearF :
      (fun s : ℝ => (finiteBallRayContinuous n R g hg s) ω) =ᶠ[𝓝 t]
        (fun s : ℝ => g (s • (ω : GLEuclidean n))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simp [finiteBallRayContinuous, hs]
  have hder :
      (finiteBallRayDerivativeContinuous n R g hg t) ω =
        (fderiv ℝ g (t • (ω : GLEuclidean n)))
          (ω : GLEuclidean n) := by
    simp [finiteBallRayDerivativeContinuous, ht]
  rw [hder]
  exact hcomp.congr_of_eventuallyEq hnearF

/-- Finite-ball version. The bridge family only needs an `L²` representative
at radii outside the ball; its derivative is determined by the actual
punctured-`C¹` field at each interior positive radius. -/
theorem scalarSphereFamilyTrace_ray_hasDerivAt_finiteBall (n : ℕ)
    (R : ℝ) (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hmem : ∀ s : ℝ, MemLp
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        g (s • (ω : GLEuclidean n))) 2 (unitSphereMeasure n))
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt
      (scalarSphereFamilyTrace n (fun s x => g (s • x)) hmem)
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (finiteBallRayDerivativeContinuous n R g hg r)) r := by
  have hT : HasDerivAt
      (fun s : ℝ =>
        (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
          (finiteBallRayContinuous n R g hg s))
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (finiteBallRayDerivativeContinuous n R g hg r)) r := by
    let T : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) →L[ℝ]
        UnitSphereL2 n := ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ
    simpa only [T] using T.hasFDerivAt.comp_hasDerivAt r
      (finiteBallRayContinuous_hasDerivAt n R g hg r hr)
  have heq :
      (scalarSphereFamilyTrace n (fun s x => g (s • x)) hmem) =ᶠ[𝓝 r]
      (fun s => (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (finiteBallRayContinuous n R g hg s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    apply Lp.ext
    have hc := ContinuousMap.coeFn_toLp
      (p := 2) (μ := unitSphereMeasure n) (𝕜 := ℝ)
      (finiteBallRayContinuous n R g hg s)
    have hm := (hmem s).coeFn_toLp
    have hc' :
        ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
          (finiteBallRayContinuous n R g hg s) : UnitSphereL2 n) =ᶠ[ae (unitSphereMeasure n)]
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          g (s • (ω : GLEuclidean n))) := by
      simpa [finiteBallRayContinuous, hs] using hc
    exact hm.trans hc'.symm
  exact hT.congr_of_eventuallyEq heq

/-- A radial family may be defined separately outside the open interval
`(0,R)`.  If it agrees there with the actual ray trace of a punctured-`C¹`
field, its `L²` derivative at every interior radius is still the concrete
radial Fréchet derivative.  This permits an explicit boundary-compatible
family with honest `L²` values at every real radius. -/
theorem scalarSphereFamilyTrace_hasDerivAt_of_local_ray_eq (n : ℕ)
    (R : ℝ) (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (family : ℝ → GLEuclidean n → ℝ)
    (hmem : ∀ s : ℝ, MemLp
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        family s ω) 2 (unitSphereMeasure n))
    (hlocal : ∀ s ∈ Ioo (0 : ℝ) R,
      ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
        family s ω = g (s • (ω : GLEuclidean n)))
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt (scalarSphereFamilyTrace n family hmem)
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (finiteBallRayDerivativeContinuous n R g hg r)) r := by
  have hT : HasDerivAt
      (fun s : ℝ =>
        (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
          (finiteBallRayContinuous n R g hg s))
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (finiteBallRayDerivativeContinuous n R g hg r)) r := by
    let T : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) →L[ℝ]
        UnitSphereL2 n := ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ
    simpa only [T] using T.hasFDerivAt.comp_hasDerivAt r
      (finiteBallRayContinuous_hasDerivAt n R g hg r hr)
  have heq :
      (scalarSphereFamilyTrace n family hmem) =ᶠ[𝓝 r]
      (fun s => (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (finiteBallRayContinuous n R g hg s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    apply Lp.ext
    have hc := ContinuousMap.coeFn_toLp
      (p := 2) (μ := unitSphereMeasure n) (𝕜 := ℝ)
      (finiteBallRayContinuous n R g hg s)
    have hm := (hmem s).coeFn_toLp
    have hc' :
        ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
          (finiteBallRayContinuous n R g hg s) : UnitSphereL2 n) =ᶠ[ae (unitSphereMeasure n)]
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          family s ω) := by
      simpa [finiteBallRayContinuous, hs, hlocal s hs] using hc
    exact hm.trans hc'.symm
  exact hT.congr_of_eventuallyEq heq

/-- Public form of the local-equivalence radial derivative theorem using
the named `L²` derivative representative. -/
theorem scalarSphereFamilyTrace_hasDerivAt_finiteBallDerivativeL2 (n : ℕ)
    (R : ℝ) (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (family : ℝ → GLEuclidean n → ℝ)
    (hmem : ∀ s : ℝ, MemLp
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        family s ω) 2 (unitSphereMeasure n))
    (hlocal : ∀ s ∈ Ioo (0 : ℝ) R,
      ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
        family s ω = g (s • (ω : GLEuclidean n)))
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt (scalarSphereFamilyTrace n family hmem)
      (finiteBallRayDerivativeL2 n R g hg r) r :=
  scalarSphereFamilyTrace_hasDerivAt_of_local_ray_eq n R g hg
    family hmem hlocal r hr

end

end BrezisOP6
