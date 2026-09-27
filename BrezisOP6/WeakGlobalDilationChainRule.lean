import BrezisOP6.WeakBallDilationChainRule

/-!
# Dilation of global zero-extension weak gradients and fixed traces

The fixed-trace condition is expressed by the global distributional
gradient of the zero extension of the competitor difference.  Positive
dilation preserves that identity and therefore preserves fixed trace.
-/

namespace BrezisOP6

open MeasureTheory Metric Set
open scoped Topology

noncomputable section

private theorem global_dilate_integral (n : ℕ) (ε : ℝ)
    (hε : 0 < ε) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : GLEuclidean n → F) :
    (∫ x, f (ε • x) ∂(volume : Measure (GLEuclidean n))) =
      (ε ^ n)⁻¹ •
        (∫ y, f y ∂(volume : Measure (GLEuclidean n))) := by
  simpa only [show Module.finrank ℝ (GLEuclidean n) = n by simp] using
    (Measure.integral_comp_smul_of_nonneg
      (volume : Measure (GLEuclidean n)) f ε (hR := hε.le))

/-- The full-space weak-gradient certificate is stable under positive
dilation, with its distributional gradient multiplied by `ε`. -/
theorem HasGlobalWeakGradient.dilate
    (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (hG : HasGlobalWeakGradient n u G) :
    HasGlobalWeakGradient n
      (fun x => u (ε • x))
      (fun x => ε • G (ε • x)) := by
  rcases hG with ⟨huMeas, hgradMeas, huL2, huL4, hgradL2, hweak⟩
  have hqm := Measure.quasiMeasurePreserving_smul
    (volume : Measure (GLEuclidean n)) hε.ne'
  have huMeas' : AEStronglyMeasurable (fun x => u (ε • x)) volume :=
    huMeas.comp_quasiMeasurePreserving hqm
  have hgradMeas' : AEStronglyMeasurable (fun x => ε • G (ε • x)) volume :=
    (hgradMeas.comp_quasiMeasurePreserving hqm).const_smul ε
  have huL2' : Integrable (fun x => ‖u (ε • x)‖ ^ 2) volume :=
    huL2.comp_smul hε.ne'
  have huL4' : Integrable (fun x => ‖u (ε • x)‖ ^ 4) volume :=
    huL4.comp_smul hε.ne'
  have hgradComp : Integrable (fun x => weakGradientSq n G (ε • x)) volume :=
    hgradL2.comp_smul hε.ne'
  have hgradL2' : Integrable
      (weakGradientSq n (fun x => ε • G (ε • x))) volume := by
    have hfun : weakGradientSq n (fun x => ε • G (ε • x)) =
        fun x => ε ^ 2 * weakGradientSq n G (ε • x) := by
      funext x
      exact weakGradientSq_dilate n ε G x
    rw [hfun]
    exact hgradComp.const_mul (ε ^ 2)
  refine ⟨huMeas', hgradMeas', huL2', huL4', hgradL2', ?_⟩
  intro φ hφ i
  let ψ : GLEuclidean n → ℝ := fun y => φ (ε⁻¹ • y)
  have hψ : C1ScalarCompactTest n ψ :=
    C1ScalarCompactTest_comp_smul n φ hφ ε⁻¹ (inv_pos.mpr hε)
  obtain ⟨hL, hR, hIBP⟩ := hweak ψ hψ i
  let e : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
  let L : GLEuclidean n → GLEuclidean n :=
    fun y => (fderiv ℝ ψ y) e • u y
  let H : GLEuclidean n → GLEuclidean n :=
    fun y => ψ y • G y e
  have hψD (x : GLEuclidean n) :
      (fderiv ℝ ψ (ε • x)) e =
        ε⁻¹ * (fderiv ℝ φ x) e := by
    simpa [ψ, e, smul_smul, hε.ne'] using
      (scalarTest_fderiv_comp_smul n φ ε⁻¹ (ε • x) i)
  have hψV (x : GLEuclidean n) : ψ (ε • x) = φ x := by
    simp [ψ, smul_smul, hε.ne']
  have hLeftFun :
      (fun x => (fderiv ℝ φ x) e • u (ε • x)) =
        fun x => ε • L (ε • x) := by
    funext x
    dsimp [L]
    rw [hψD]
    simp [smul_smul, hε.ne']
  have hRightFun :
      (fun x => φ x • (ε • G (ε • x)) e) =
        fun x => ε • H (ε • x) := by
    funext x
    dsimp [H]
    rw [hψV]
    exact smul_comm _ _ _
  have hLscaled : Integrable (fun x => L (ε • x)) volume :=
    hL.comp_smul hε.ne'
  have hRscaled : Integrable (fun x => H (ε • x)) volume :=
    hR.comp_smul hε.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [hLeftFun]
    exact Integrable.smul ε hLscaled
  · rw [hRightFun]
    exact Integrable.smul ε hRscaled
  · rw [hLeftFun, hRightFun, integral_smul, integral_smul,
      global_dilate_integral n ε hε L,
      global_dilate_integral n ε hε H]
    change ε • ((ε ^ n)⁻¹ • ∫ y, L y) =
      -(ε • ((ε ^ n)⁻¹ • ∫ y, H y))
    rw [show (∫ y, L y) = -(∫ y, H y) from hIBP]
    simp

/-- Zero extension of a field difference commutes with positive dilation
of the domain and its ball. -/
theorem zeroExtendedDifference_dilate
    (n : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (u v : GLEuclidean n → GLEuclidean n) :
    zeroExtendedDifference n (R / ε)
      (fun x => u (ε • x)) (fun x => v (ε • x)) =
        fun x => zeroExtendedDifference n R u v (ε • x) := by
  funext x
  by_cases hx : x ∈ Metric.ball (0 : GLEuclidean n) (R / ε)
  · have hxe : ε • x ∈ Metric.ball (0 : GLEuclidean n) R :=
      (ball_dilate_membership n R ε hε x).2 hx
    simp [zeroExtendedDifference, hx, hxe]
  · have hxe : ε • x ∉ Metric.ball (0 : GLEuclidean n) R := by
      intro he
      exact hx ((ball_dilate_membership n R ε hε x).1 he)
    simp [zeroExtendedDifference, hx, hxe]

/-- The weak-gradient zero extension commutes with positive dilation;
the scalar factor is the distributional chain-rule factor. -/
theorem zeroExtendedGradientDifference_dilate
    (n : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (G H : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) :
    zeroExtendedGradientDifference n (R / ε)
      (fun x => ε • G (ε • x))
      (fun x => ε • H (ε • x)) =
        fun x => ε • zeroExtendedGradientDifference n R G H (ε • x) := by
  funext x
  by_cases hx : x ∈ Metric.ball (0 : GLEuclidean n) (R / ε)
  · have hxe : ε • x ∈ Metric.ball (0 : GLEuclidean n) R :=
      (ball_dilate_membership n R ε hε x).2 hx
    simp [zeroExtendedGradientDifference, hx, hxe, smul_sub]
  · have hxe : ε • x ∉ Metric.ball (0 : GLEuclidean n) R := by
      intro he
      exact hx ((ball_dilate_membership n R ε hε x).1 he)
    simp only [zeroExtendedGradientDifference, if_neg hx, if_neg hxe]
    ext z
    simp [ContinuousLinearMap.smul_apply]

/-- Fixed weak trace is preserved by simultaneous positive dilation of
the prescribed base field and its competitor. -/
def WeakFixedTraceCompetitor.dilate
    {n : ℕ} {R : ℝ}
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base)
    (ε : ℝ) (hε : 0 < ε) :
    WeakFixedTraceCompetitor (base.dilate ε hε) := by
  let V : WeakH1L4BallField n (R / ε) := U.field.dilate ε hε
  refine ⟨V, ?_⟩
  have htrace := HasGlobalWeakGradient.dilate n ε hε
    (zeroExtendedDifference n R U.field.u base.u)
    (zeroExtendedGradientDifference n R U.field.grad base.grad)
    U.zeroTrace
  change HasGlobalWeakGradient n
    (zeroExtendedDifference n (R / ε)
      (fun x => U.field.u (ε • x))
      (fun x => base.u (ε • x)))
    (zeroExtendedGradientDifference n (R / ε)
      (fun x => ε • U.field.grad (ε • x))
      (fun x => ε • base.grad (ε • x)))
  rw [zeroExtendedDifference_dilate n R ε hε,
    zeroExtendedGradientDifference_dilate n R ε hε]
  exact htrace

end

end BrezisOP6
