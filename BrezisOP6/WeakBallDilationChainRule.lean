import BrezisOP6.WeakDilationTests
import BrezisOP6.WeakEnergyEpsilonScaling

/-!
# Dilation of distributional weak gradients on Euclidean balls

The change of variables for the energy density alone does not certify a
weak gradient. This file proves that the distributional identity itself
survives positive dilation, including the integrability of both test
products. Fixed-trace compatibility is a separate boundary assertion.
-/

namespace BrezisOP6

open MeasureTheory Metric Set
open scoped Topology Pointwise

noncomputable section

theorem ball_dilate_membership (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) (x : GLEuclidean n) :
    ε • x ∈ Metric.ball (0 : GLEuclidean n) R ↔
      x ∈ Metric.ball (0 : GLEuclidean n) (R / ε) := by
  simp only [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hε]
  simpa only [mul_comm] using (lt_div_iff₀ hε).symm

private theorem ball_dilate_integrable (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) {F : Type*} [NormedAddCommGroup F]
    (f : GLEuclidean n → F)
    (hf : Integrable f (weakBallMeasure n R)) :
    Integrable (fun x => f (ε • x))
      (weakBallMeasure n (R / ε)) := by
  let B : Set (GLEuclidean n) := Metric.ball 0 R
  let C : Set (GLEuclidean n) := Metric.ball 0 (R / ε)
  have hglob : Integrable (B.indicator f) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hf
  have hcomp : Integrable (fun x => B.indicator f (ε • x)) volume :=
    hglob.comp_smul hε.ne'
  have hfun : (fun x => B.indicator f (ε • x)) =
      C.indicator (fun x => f (ε • x)) := by
    funext x
    by_cases hx : x ∈ C
    · have hxe : ε • x ∈ B := (ball_dilate_membership n R ε hε x).2 hx
      simp [Set.indicator, hx, hxe]
    · have hxe : ε • x ∉ B := by
        intro he
        exact hx ((ball_dilate_membership n R ε hε x).1 he)
      simp [Set.indicator, hx, hxe]
  rw [hfun] at hcomp
  exact (integrable_indicator_iff measurableSet_ball).mp hcomp

private theorem ball_dilate_aestronglyMeasurable (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) {F : Type*} [NormedAddCommGroup F]
    (f : GLEuclidean n → F)
    (hf : AEStronglyMeasurable f (weakBallMeasure n R)) :
    AEStronglyMeasurable (fun x => f (ε • x))
      (weakBallMeasure n (R / ε)) := by
  let B : Set (GLEuclidean n) := Metric.ball 0 R
  let C : Set (GLEuclidean n) := Metric.ball 0 (R / ε)
  have hglob : AEStronglyMeasurable (B.indicator f) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_ball).mpr hf
  have hcomp : AEStronglyMeasurable
      (fun x => B.indicator f (ε • x)) volume :=
    hglob.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume hε.ne')
  have hfun : (fun x => B.indicator f (ε • x)) =
      C.indicator (fun x => f (ε • x)) := by
    funext x
    by_cases hx : x ∈ C
    · have hxe : ε • x ∈ B := (ball_dilate_membership n R ε hε x).2 hx
      simp [Set.indicator, hx, hxe]
    · have hxe : ε • x ∉ B := by
        intro he
        exact hx ((ball_dilate_membership n R ε hε x).1 he)
      simp [Set.indicator, hx, hxe]
  rw [hfun] at hcomp
  exact (aestronglyMeasurable_indicator_iff measurableSet_ball).mp hcomp

private theorem ball_dilate_integral (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (f : GLEuclidean n → F) :
    (∫ x, f (ε • x) ∂(weakBallMeasure n (R / ε))) =
      (ε ^ n)⁻¹ •
        (∫ y, f y ∂(weakBallMeasure n R)) := by
  have hball := epsilon_smul_ball n R ε hε
  simpa only [weakBallMeasure, hball,
    show Module.finrank ℝ (GLEuclidean n) = n by simp] using
    (Measure.setIntegral_comp_smul_of_pos
      (volume : Measure (GLEuclidean n)) f
      (Metric.ball (0 : GLEuclidean n) (R / ε)) hε)

/-- An interior compactly supported test on the dilated ball pulls back
to one on the original ball. -/
theorem C1ScalarInteriorTest_dilate_inverse (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) (φ : GLEuclidean n → ℝ)
    (hφ : C1ScalarInteriorTest n (R / ε) φ) :
    C1ScalarInteriorTest n R (fun y => φ (ε⁻¹ • y)) := by
  obtain ⟨hφdiff, ρ, hρnonneg, hρlt, hzero⟩ := hφ
  refine ⟨hφdiff.comp (contDiff_const_smul ε⁻¹), ρ * ε,
    mul_nonneg hρnonneg hε.le, ?_, ?_⟩
  · exact (lt_div_iff₀ hε).1 hρlt
  · intro y hy
    apply hzero
    have hnorm : ‖ε⁻¹ • y‖ = ε⁻¹ * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    rw [hnorm]
    simpa only [div_eq_mul_inv, mul_comm] using
      (le_div_iff₀ hε).2 hy

/-- Positive dilation preserves the actual distributional weak derivative
on the correspondingly dilated ball. -/
theorem HasWeakGradientOnBall.dilate
    (n : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (hG : HasWeakGradientOnBall n R u G) :
    HasWeakGradientOnBall n (R / ε)
      (fun x => u (ε • x))
      (fun x => ε • G (ε • x)) := by
  intro φ hφ i
  let ψ : GLEuclidean n → ℝ := fun y => φ (ε⁻¹ • y)
  have hψ : C1ScalarInteriorTest n R ψ :=
    C1ScalarInteriorTest_dilate_inverse n R ε hε φ hφ
  obtain ⟨hL, hR, hIBP⟩ := hG ψ hψ i
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
  have hLscaled : Integrable (fun x => L (ε • x))
      (weakBallMeasure n (R / ε)) :=
    ball_dilate_integrable n R ε hε L hL
  have hRscaled : Integrable (fun x => H (ε • x))
      (weakBallMeasure n (R / ε)) :=
    ball_dilate_integrable n R ε hε H hR
  refine ⟨?_, ?_, ?_⟩
  · rw [hLeftFun]
    exact Integrable.smul ε hLscaled
  · rw [hRightFun]
    exact Integrable.smul ε hRscaled
  · rw [hLeftFun, hRightFun, integral_smul, integral_smul,
      ball_dilate_integral n R ε hε L,
      ball_dilate_integral n R ε hε H]
    change ε • ((ε ^ n)⁻¹ • ∫ y, L y ∂(weakBallMeasure n R)) =
      -(ε • ((ε ^ n)⁻¹ • ∫ y, H y ∂(weakBallMeasure n R)))
    rw [show (∫ y, L y ∂(weakBallMeasure n R)) =
      -(∫ y, H y ∂(weakBallMeasure n R)) from hIBP]
    simp

/-- A certified Sobolev field remains a certified Sobolev field under
positive domain dilation, with the correctly scaled weak gradient. -/
def WeakH1L4BallField.dilate {n : ℕ} {R : ℝ}
    (U : WeakH1L4BallField n R) (ε : ℝ) (hε : 0 < ε) :
    WeakH1L4BallField n (R / ε) := by
  let v : GLEuclidean n → GLEuclidean n := fun x => U.u (ε • x)
  let H : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n :=
    fun x => ε • U.grad (ε • x)
  have huMeas : AEStronglyMeasurable v (weakBallMeasure n (R / ε)) :=
    ball_dilate_aestronglyMeasurable n R ε hε U.u U.uMeas
  have hgradMeas : AEStronglyMeasurable H (weakBallMeasure n (R / ε)) :=
    (ball_dilate_aestronglyMeasurable n R ε hε U.grad U.gradMeas).const_smul ε
  have huL2 : Integrable (fun x => ‖v x‖ ^ 2)
      (weakBallMeasure n (R / ε)) :=
    ball_dilate_integrable n R ε hε (fun y => ‖U.u y‖ ^ 2) U.uL2
  have huL4 : Integrable (fun x => ‖v x‖ ^ 4)
      (weakBallMeasure n (R / ε)) :=
    ball_dilate_integrable n R ε hε (fun y => ‖U.u y‖ ^ 4) U.uL4
  have hgradComp : Integrable
      (fun x => weakGradientSq n U.grad (ε • x))
      (weakBallMeasure n (R / ε)) :=
    ball_dilate_integrable n R ε hε (weakGradientSq n U.grad) U.gradL2
  have hgradL2 : Integrable (weakGradientSq n H)
      (weakBallMeasure n (R / ε)) := by
    have hfun : weakGradientSq n H =
        fun x => ε ^ 2 * weakGradientSq n U.grad (ε • x) := by
      funext x
      exact weakGradientSq_dilate n ε U.grad x
    rw [hfun]
    exact hgradComp.const_mul (ε ^ 2)
  exact ⟨v, H, huMeas, hgradMeas, huL2, huL4,
    hgradL2,
    HasWeakGradientOnBall.dilate n R ε hε U.u U.grad U.weakDerivative⟩

/-- The existing energy Jacobian now applies to an actual certified weak
field, rather than only to a candidate gradient. -/
theorem WeakH1L4BallField.dilate_energy_scaling
    {n : ℕ} {R : ℝ} (U : WeakH1L4BallField n R)
    (ε : ℝ) (hε : 0 < ε) :
    ε ^ n * (U.dilate ε hε).energy =
      ε ^ 2 * weakBallEnergyEpsilon n R ε U.u U.grad := by
  change ε ^ n * weakBallEnergy n (R / ε)
      (fun x => U.u (ε • x)) (fun x => ε • U.grad (ε • x)) =
    ε ^ 2 * weakBallEnergyEpsilon n R ε U.u U.grad
  exact weakBallEnergyEpsilon_scaling n R ε hε U.u U.grad

end

end BrezisOP6
