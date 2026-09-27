import BrezisOP6.SphereRadialL2Differentiability

/-!
# Radial `L²` differentiability away from the origin

The quotient field used in the finite-ball argument can be singular at the
origin.  At a positive radius, only its `C¹` regularity on the punctured
ambient space is needed.  The proof repeats the continuous-function-valued
FTC argument on the positive radius interval, so no value or derivative at
the origin enters the conclusion.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set
open scoped Topology

private theorem continuousMap_hasDerivAt_of_pointwise_pos
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (F D : ℝ → C(α, ℝ))
    (hD : ContinuousOn D (Ioi (0 : ℝ)))
    (hpoint : ∀ (t : ℝ), 0 < t → ∀ (ω : α),
      HasDerivAt (fun s : ℝ => F s ω) (D t ω) t)
    (r : ℝ) (hr : 0 < r) : HasDerivAt F (D r) r := by
  have hint (s : ℝ) (hs : 0 < s) : IntervalIntegrable D volume r s := by
    apply ContinuousOn.intervalIntegrable
    apply hD.mono
    intro t ht
    rcases le_total r s with hrs | hsr
    · rw [uIcc_of_le hrs] at ht
      exact lt_of_lt_of_le hr ht.1
    · rw [uIcc_of_ge hsr] at ht
      exact lt_of_lt_of_le hs ht.1
  have hFTCeq (s : ℝ) (hs : 0 < s) :
      (∫ t in r..s, D t) = F s - F r := by
    ext ω
    have hevalCont : ContinuousOn (fun t : ℝ => D t ω) (Ioi (0 : ℝ)) :=
      (ContinuousMap.evalCLM ℝ ω).continuous.comp_continuousOn' hD
    have hpointInt :
        (∫ t in r..s, D t ω) = F s ω - F r ω := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        have htpos : 0 < t := by
          rcases le_total r s with hrs | hsr
          · rw [uIcc_of_le hrs] at ht
            exact lt_of_lt_of_le hr ht.1
          · rw [uIcc_of_ge hsr] at ht
            exact lt_of_lt_of_le hs ht.1
        exact hpoint t htpos ω
      · exact (hevalCont.mono (by
          intro t ht
          rcases le_total r s with hrs | hsr
          · rw [uIcc_of_le hrs] at ht
            exact lt_of_lt_of_le hr ht.1
          · rw [uIcc_of_ge hsr] at ht
            exact lt_of_lt_of_le hs ht.1)).intervalIntegrable
    calc
      (∫ t in r..s, D t) ω =
          ∫ t in r..s, D t ω := by
            simpa only [ContinuousMap.evalCLM_apply] using
              ((ContinuousMap.evalCLM ℝ ω).intervalIntegral_comp_comm
                (hint s hs)).symm
      _ = F s ω - F r ω := hpointInt
      _ = (F s - F r) ω := rfl
  have hDAt : ContinuousAt D r :=
    hD.continuousAt (isOpen_Ioi.mem_nhds hr)
  have hDMeas : StronglyMeasurableAtFilter D (𝓝 r) volume :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hD) r hr
  have hFTC :
      HasDerivAt (fun s : ℝ => ∫ t in r..s, D t)
        (D r) r :=
    intervalIntegral.integral_hasDerivAt_right
      (hint r hr) hDMeas hDAt
  have heq :
      (fun s : ℝ => ∫ t in r..s, D t) =ᶠ[𝓝 r]
        (fun s : ℝ => F s - F r) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact hFTCeq s hs
  have hdiff : HasDerivAt (fun s : ℝ => F s - F r) (D r) r :=
    hFTC.congr_of_eventuallyEq heq.symm
  simpa only [sub_add_cancel] using hdiff.add_const (F r)

private theorem sphereRay_ne_zero (n : ℕ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (s : ℝ) (hs : 0 < s) :
    s • (ω : GLEuclidean n) ≠ 0 := by
  have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  apply norm_ne_zero_iff.mp
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hω, hs.ne']

/-- Positive-radius continuous trace of a field that is `C¹` away from
the ambient origin.  Its value at nonpositive radii is irrelevant to the
local differentiability statement. -/
def scalarSphereRayContinuousPos (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)))
    (s : ℝ) : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) := by
  by_cases hs : 0 < s
  · have hRay : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          s • (ω : GLEuclidean n)) :=
      (continuous_const_smul s).comp continuous_subtype_val
    exact ⟨fun ω => g (s • (ω : GLEuclidean n)),
      hg.continuousOn.comp_continuous hRay
        (fun ω => sphereRay_ne_zero n ω s hs)⟩
  · exact 0

/-- The continuous radial derivative of the positive-radius trace. -/
def scalarSphereRayDerivativeContinuousPos (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)))
    (s : ℝ) : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) := by
  by_cases hs : 0 < s
  · have hRay : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          s • (ω : GLEuclidean n)) :=
      (continuous_const_smul s).comp continuous_subtype_val
    have hF : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          fderiv ℝ g (s • (ω : GLEuclidean n))) :=
      (hg.continuousOn_fderiv_of_isOpen isOpen_compl_singleton
        (by norm_num)).comp_continuous hRay
        (fun ω => sphereRay_ne_zero n ω s hs)
    exact ⟨fun ω => (fderiv ℝ g (s • (ω : GLEuclidean n)))
      (ω : GLEuclidean n), hF.clm_apply continuous_subtype_val⟩
  · exact 0

/-- The positive-radius derivative representative varies continuously
in the sphere's sup norm. -/
theorem scalarSphereRayDerivativeContinuousPos_continuousOn (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n))) :
    ContinuousOn (scalarSphereRayDerivativeContinuousPos n g hg)
      (Ioi (0 : ℝ)) := by
  let S := Metric.sphere (0 : GLEuclidean n) 1
  let U : Set (ℝ × S) := Ioi (0 : ℝ) ×ˢ univ
  have hRay : Continuous (fun p : ℝ × S =>
      p.1 • (p.2 : GLEuclidean n)) :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  have hRayMaps : MapsTo
      (fun p : ℝ × S => p.1 • (p.2 : GLEuclidean n))
      U ({0}ᶜ : Set (GLEuclidean n)) := by
    intro p hp
    exact sphereRay_ne_zero n p.2 p.1 hp.1
  have hF : ContinuousOn (fun p : ℝ × S =>
      fderiv ℝ g (p.1 • (p.2 : GLEuclidean n))) U :=
    (hg.continuousOn_fderiv_of_isOpen isOpen_compl_singleton
      (by norm_num)).comp hRay.continuousOn hRayMaps
  have hDunc : ContinuousOn (fun p : ℝ × S =>
      (fderiv ℝ g (p.1 • (p.2 : GLEuclidean n)))
        (p.2 : GLEuclidean n)) U :=
    hF.clm_apply (continuous_subtype_val.comp continuous_snd).continuousOn
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  apply hDunc.congr
  intro p hp
  change (scalarSphereRayDerivativeContinuousPos n g hg p.1) p.2 = _
  simp [scalarSphereRayDerivativeContinuousPos, Set.mem_Ioi.mp hp.1]

/-- At every positive radius, a field that is `C¹` away from zero has a
radially differentiable continuous sphere trace. -/
theorem scalarSphereRayContinuousPos_hasDerivAt (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)))
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (scalarSphereRayContinuousPos n g hg)
      (scalarSphereRayDerivativeContinuousPos n g hg r) r := by
  refine continuousMap_hasDerivAt_of_pointwise_pos
    (scalarSphereRayContinuousPos n g hg)
    (scalarSphereRayDerivativeContinuousPos n g hg)
    (scalarSphereRayDerivativeContinuousPos_continuousOn n g hg)
    ?_ r hr
  intro t ht ω
  have hray : HasDerivAt
      (fun s : ℝ => s • (ω : GLEuclidean n))
      (ω : GLEuclidean n) t := by
    simpa using (hasDerivAt_id t).smul_const (ω : GLEuclidean n)
  have hx : t • (ω : GLEuclidean n) ≠ 0 :=
    sphereRay_ne_zero n ω t ht
  have hf : HasFDerivAt g (fderiv ℝ g (t • (ω : GLEuclidean n)))
      (t • (ω : GLEuclidean n)) :=
    ((hg.differentiableOn_one).differentiableAt
      (isOpen_compl_singleton.mem_nhds hx)).hasFDerivAt
  have hcomp := hf.comp_hasDerivAt t hray
  have hnearF :
      (fun s : ℝ => (scalarSphereRayContinuousPos n g hg s) ω) =ᶠ[𝓝 t]
        (fun s : ℝ => g (s • (ω : GLEuclidean n))) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    simp [scalarSphereRayContinuousPos, Set.mem_Ioi.mp hs]
  have hder :
      (scalarSphereRayDerivativeContinuousPos n g hg t) ω =
        (fderiv ℝ g (t • (ω : GLEuclidean n)))
          (ω : GLEuclidean n) := by
    simp [scalarSphereRayDerivativeContinuousPos, ht]
  rw [hder]
  exact hcomp.congr_of_eventuallyEq hnearF

/-- The actual punctured-field sphere trace is differentiable in `L²`
at every positive radius, with the derivative represented by its radial
Fréchet derivative. -/
theorem scalarSphereRayL2Pos_hasDerivAt (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)))
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt
      (fun s : ℝ =>
        (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
          (scalarSphereRayContinuousPos n g hg s))
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayDerivativeContinuousPos n g hg r)) r := by
  let T : C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) →L[ℝ]
      UnitSphereL2 n := ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ
  have hT : HasFDerivAt T T (scalarSphereRayContinuousPos n g hg r) :=
    T.hasFDerivAt
  simpa only [T] using hT.comp_hasDerivAt r
    (scalarSphereRayContinuousPos_hasDerivAt n g hg r hr)

/-- The actual ray trace belongs to `L²` at every radius, including zero.
The value of the ambient field at the origin need not satisfy any regularity
assumption: at radius zero the trace is constant. -/
def scalarSphereRayMemLpPunctured (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)))
    (s : ℝ) :
    MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      g (s • (ω : GLEuclidean n))) 2 (unitSphereMeasure n) := by
  by_cases hs : s = 0
  · subst s
    have hcont : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          g ((0 : ℝ) • (ω : GLEuclidean n))) := by
      simpa using (continuous_const : Continuous
        (fun _ : Metric.sphere (0 : GLEuclidean n) 1 =>
          g (0 : GLEuclidean n)))
    exact hcont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · have hRay : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          s • (ω : GLEuclidean n)) :=
      (continuous_const_smul s).comp continuous_subtype_val
    have hRayNe (ω : Metric.sphere (0 : GLEuclidean n) 1) :
        s • (ω : GLEuclidean n) ≠ 0 := by
      have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
        mem_sphere_zero_iff_norm.mp ω.property
      have hωne : (ω : GLEuclidean n) ≠ 0 := by
        apply norm_ne_zero_iff.mp
        rw [hω]
        norm_num
      exact smul_ne_zero hs hωne
    have hcont : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          g (s • (ω : GLEuclidean n))) :=
      hg.continuousOn.comp_continuous hRay hRayNe
    exact hcont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- At positive radii, the positive-radius continuous trace and the bridge's
`MemLp.toLp` trace are the same concrete `L²` element. -/
theorem scalarSphereRayL2Pos_eq_familyTrace (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)))
    (r : ℝ) (hr : 0 < r) :
    (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
      (scalarSphereRayContinuousPos n g hg r) =
    scalarSphereFamilyTrace n
      (fun s x => g (s • x))
      (scalarSphereRayMemLpPunctured n g hg) r := by
  apply Lp.ext
  have hc := ContinuousMap.coeFn_toLp
    (p := 2) (μ := unitSphereMeasure n) (𝕜 := ℝ)
    (scalarSphereRayContinuousPos n g hg r)
  have hm := (scalarSphereRayMemLpPunctured n g hg r).coeFn_toLp
  have hc' :
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayContinuousPos n g hg r) : UnitSphereL2 n) =ᶠ[ae (unitSphereMeasure n)]
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        g (r • (ω : GLEuclidean n))) := by
    simpa [scalarSphereRayContinuousPos, hr] using hc
  exact hc'.trans hm.symm

/-- The bridge trace of an actual punctured-`C¹` field has its radial `L²`
derivative at every positive radius. -/
theorem scalarSphereFamilyTrace_ray_hasDerivAt_punctured (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)))
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt
      (scalarSphereFamilyTrace n
        (fun s x => g (s • x))
        (scalarSphereRayMemLpPunctured n g hg))
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayDerivativeContinuousPos n g hg r)) r := by
  have heq :
      (scalarSphereFamilyTrace n
        (fun s x => g (s • x))
        (scalarSphereRayMemLpPunctured n g hg)) =ᶠ[𝓝 r]
      (fun s => (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayContinuousPos n g hg s)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact (scalarSphereRayL2Pos_eq_familyTrace n g hg s hs).symm
  exact (scalarSphereRayL2Pos_hasDerivAt n g hg r hr).congr_of_eventuallyEq heq

/-- Coordinatewise bridge trace differentiability for a vector field that
is `C¹` on the punctured ambient space. -/
theorem vectorSphereFamilyTrace_ray_hasDerivAt_punctured (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z ({0}ᶜ : Set (GLEuclidean n)))
    (k : Fin n) (r : ℝ) (hr : 0 < r) :
    let g : GLEuclidean n → ℝ := fun x => (z x) k
    let hg : ContDiffOn ℝ 1 g ({0}ᶜ : Set (GLEuclidean n)) := by
      simpa only [g, EuclideanSpace.coe_proj, Function.comp_def] using
        (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
    HasDerivAt
      (scalarSphereFamilyTrace n
        (fun s x => g (s • x))
        (scalarSphereRayMemLpPunctured n g hg))
      ((ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ)
        (scalarSphereRayDerivativeContinuousPos n g hg r)) r := by
  exact scalarSphereFamilyTrace_ray_hasDerivAt_punctured n
    (fun x : GLEuclidean n => (z x) k)
    (by
      simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
        (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz) r hr

end

end BrezisOP6
