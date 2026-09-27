import BrezisOP6.SphereScalarBridgeSurface

/-!
# Measurability of the actual coordinatewise spherical bridge

On the punctured cylinder, the bridge integrand is a continuous expression
in the field and its Fréchet derivative.  Extending this expression by zero
outside the cylinder permits an ordinary product-measure argument.  This
also avoids making any regularity claim about the artificial radius values
of `finiteBallSphereFamily` outside the physical ball.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

private def regularScalarSphereBridgePointwise
    (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (k : Fin (m + 3))
    (p : ℝ × Metric.sphere (0 : GLEuclidean (m + 3)) 1) : ℝ :=
  let r := p.1
  let ω : GLEuclidean (m + 3) := p.2
  let g : GLEuclidean (m + 3) → ℝ := fun x => (z x) k
  let D := fderiv ℝ g (r • ω)
  r ^ (m + 2) * (f r ^ 2 - F r ^ 2) * (D ω) ^ 2 +
    r ^ m * (f r ^ 2 - F r ^ 2) *
      (‖r • D‖ ^ 2 - ((r • D) ω) ^ 2 -
        (m + 2 : ℝ) * g (r • ω) ^ 2)

private theorem regularScalarSphereBridgePointwise_continuousOn
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hf : ContinuousOn f (Ioo (0 : ℝ) R))
    (hF : ContinuousOn F (Ioo (0 : ℝ) R))
    (k : Fin (m + 3)) :
    ContinuousOn (regularScalarSphereBridgePointwise m f F z k)
      (Ioo (0 : ℝ) R ×ˢ (univ : Set
        (Metric.sphere (0 : GLEuclidean (m + 3)) 1))) := by
  let S := Metric.sphere (0 : GLEuclidean (m + 3)) 1
  let U : Set (ℝ × S) := Ioo (0 : ℝ) R ×ˢ univ
  let g : GLEuclidean (m + 3) → ℝ := fun x => (z x) k
  let ray : ℝ × S → GLEuclidean (m + 3) :=
    fun p => p.1 • (p.2 : GLEuclidean (m + 3))
  have hRay : Continuous ray :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  have hMaps : MapsTo ray U
      {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    intro p hp
    have hω : ‖(p.2 : GLEuclidean (m + 3))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp p.2.property
    have hnorm : ‖p.1 • (p.2 : GLEuclidean (m + 3))‖ = p.1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1.1, hω]
      ring
    change 0 < ‖ray p‖ ∧ ‖ray p‖ < R
    rw [show ‖ray p‖ = p.1 from hnorm]
    exact hp.1
  have hopen : IsOpen
      {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hg : ContDiffOn ℝ 1 g
      {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [g, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  have hD : ContinuousOn (fun p : ℝ × S => fderiv ℝ g (ray p)) U :=
    (hg.continuousOn_fderiv_of_isOpen hopen (by norm_num)).comp
      hRay.continuousOn hMaps
  have hV : ContinuousOn (fun p : ℝ × S => g (ray p)) U :=
    hg.continuousOn.comp hRay.continuousOn hMaps
  have hDir : ContinuousOn (fun p : ℝ × S =>
      (fderiv ℝ g (ray p)) (p.2 : GLEuclidean (m + 3))) U :=
    hD.clm_apply (continuous_subtype_val.comp continuous_snd).continuousOn
  have hScaled : ContinuousOn (fun p : ℝ × S =>
      p.1 • fderiv ℝ g (ray p)) U :=
    continuous_fst.continuousOn.smul hD
  have hScaledDir : ContinuousOn (fun p : ℝ × S =>
      (p.1 • fderiv ℝ g (ray p))
        (p.2 : GLEuclidean (m + 3))) U :=
    hScaled.clm_apply
      (continuous_subtype_val.comp continuous_snd).continuousOn
  have hf' : ContinuousOn (fun p : ℝ × S => f p.1) U :=
    hf.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hF' : ContinuousOn (fun p : ℝ × S => F p.1) U :=
    hF.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hr' : ContinuousOn (fun p : ℝ × S => p.1) U :=
    continuous_fst.continuousOn
  have hd : ContinuousOn (fun p : ℝ × S =>
      f p.1 ^ 2 - F p.1 ^ 2) U :=
    (hf'.pow 2).sub (hF'.pow 2)
  have hq : ContinuousOn
      (fun p : ℝ × S =>
        p.1 ^ (m + 2) * (f p.1 ^ 2 - F p.1 ^ 2) *
            ((fderiv ℝ g (ray p)) (p.2 : GLEuclidean (m + 3))) ^ 2 +
          p.1 ^ m * (f p.1 ^ 2 - F p.1 ^ 2) *
            (‖p.1 • fderiv ℝ g (ray p)‖ ^ 2 -
              ((p.1 • fderiv ℝ g (ray p))
                (p.2 : GLEuclidean (m + 3))) ^ 2 -
              (m + 2 : ℝ) * (g (ray p)) ^ 2)) U := by
    exact (((hr'.pow (m + 2)).mul hd).mul (hDir.pow 2)).add
      (((hr'.pow m).mul hd).mul
        (((hScaled.norm.pow 2).sub (hScaledDir.pow 2)).sub
          (continuousOn_const.mul (hV.pow 2))))
  simpa only [regularScalarSphereBridgePointwise, U, ray, g] using hq

private theorem regularScalarSphereBridgePointwise_eq_actual
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (k : Fin (m + 3)) :
    regularScalarSphereBridgePointwise m f F z k (r, ω) =
      scalarSphereBridgePointwise m f F
        (fun s y => (z (s • y)) k) r ω := by
  let g : GLEuclidean (m + 3) → ℝ := fun x => (z x) k
  have hω : ‖(ω : GLEuclidean (m + 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hx : r • (ω : GLEuclidean (m + 3)) ∈
      {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    have hnorm : ‖r • (ω : GLEuclidean (m + 3))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
      ring
    change 0 < ‖r • (ω : GLEuclidean (m + 3))‖ ∧
      ‖r • (ω : GLEuclidean (m + 3))‖ < R
    rw [hnorm]
    exact hr
  have hopen : IsOpen
      {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hg : DifferentiableAt ℝ g
      (r • (ω : GLEuclidean (m + 3))) := by
    have hk : ContDiffOn ℝ 1 g
        {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} := by
      simpa only [g, Function.comp_def, EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
    exact (hk.differentiableOn_one).differentiableAt
      (hopen.mem_nhds hx)
  have hray : HasDerivAt
      (fun s : ℝ => g (s • (ω : GLEuclidean (m + 3))))
      ((fderiv ℝ g (r • (ω : GLEuclidean (m + 3))))
        (ω : GLEuclidean (m + 3))) r := by
    have hline : HasDerivAt
        (fun s : ℝ => s • (ω : GLEuclidean (m + 3)))
        (ω : GLEuclidean (m + 3)) r := by
      simpa using
        (hasDerivAt_id r).smul_const (ω : GLEuclidean (m + 3))
    exact hg.hasFDerivAt.comp_hasDerivAt r hline
  have hscaled :
      fderiv ℝ (fun y : GLEuclidean (m + 3) => g (r • y))
          (ω : GLEuclidean (m + 3)) =
        r • fderiv ℝ g (r • (ω : GLEuclidean (m + 3))) := by
    exact fderiv_comp_smul
      (f := g) (x := (ω : GLEuclidean (m + 3))) r
  unfold regularScalarSphereBridgePointwise
    scalarSphereBridgePointwise
  simp only [Prod.fst, Prod.snd, g, hray.deriv, hscaled]

/-- Actual punctured `C¹` regularity and continuous radial coefficients
make each coordinate's finite-ball spherical bridge measurable. -/
theorem finiteBall_scalarBridge_aestronglyMeasurable
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hf : ContinuousOn f (Ioo (0 : ℝ) R))
    (hF : ContinuousOn F (Ioo (0 : ℝ) R))
    (k : Fin (m + 3)) :
    AEStronglyMeasurable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      (volume.restrict (Ioc (0 : ℝ) R)) := by
  let S := Metric.sphere (0 : GLEuclidean (m + 3)) 1
  let U : Set (ℝ × S) := Ioo (0 : ℝ) R ×ˢ univ
  let q : ℝ × S → ℝ := regularScalarSphereBridgePointwise m f F z k
  let q₀ : ℝ × S → ℝ := U.piecewise q 0
  have hq : ContinuousOn q U :=
    regularScalarSphereBridgePointwise_continuousOn
      m f F R z hz hf hF k
  have hUmeas : MeasurableSet U :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hq₀ : StronglyMeasurable q₀ :=
    (hq.measurable_piecewise continuousOn_const hUmeas).stronglyMeasurable
  have hparam : StronglyMeasurable
      (fun r : ℝ => ∫ ω : S, q₀ (r, ω) ∂(unitSphereMeasure (m + 3))) :=
    (show StronglyMeasurable
      (Function.uncurry (fun r : ℝ => fun ω : S => q₀ (r, ω)))
      from hq₀).integral_prod_right
  have hRnull : ∀ᵐ r : ℝ ∂volume, r ≠ R := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      (measure_singleton R : volume {R} = 0)
  apply hparam.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae hRnull] with r hr hrR
  have hri : r ∈ Ioo (0 : ℝ) R :=
    ⟨hr.1, lt_of_le_of_ne hr.2 hrR⟩
  rw [finiteBallSphereFamily_scalarBridgeDensity_eq_actual_surface_integral
    m f F R z hz r hri k]
  apply integral_congr_ae
  filter_upwards [] with ω
  calc
    q₀ (r, ω) = q (r, ω) := by simp [q₀, U, hri]
    _ = _ := regularScalarSphereBridgePointwise_eq_actual
      m f F R z hz r hri ω k

end

end BrezisOP6
