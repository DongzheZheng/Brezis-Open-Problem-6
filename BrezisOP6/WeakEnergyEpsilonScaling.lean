import BrezisOP6.WeakDilationGradient
import BrezisOP6.EnergyEpsilonScaling

/-!
# Scaling of the weak-gradient energy integrand

This theorem concerns a field together with a *specified candidate* weak
gradient.  It is the correct algebra and Jacobian for the paper's `ε`
scaling.  Preservation of the distributional derivative identity under
dilation is an additional theorem, and is not asserted here.
-/

namespace BrezisOP6

open MeasureTheory Metric
open scoped Pointwise

noncomputable section

def weakBallEnergyEpsilon (n : ℕ) (R ε : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) : ℝ :=
  ∫ x, weakGradientSq n G x / 2 +
      (1 - ‖u x‖ ^ 2) ^ 2 / (4 * ε ^ 2)
    ∂(weakBallMeasure n R)

/-- On a smooth field equipped with its classical derivative, the weak
`ε`-energy is the concrete `ε`-energy. -/
theorem weakBallEnergyEpsilon_classical_gradient (n : ℕ) (R ε : ℝ)
    (u : GLEuclidean n → GLEuclidean n) :
    weakBallEnergyEpsilon n R ε u (fderiv ℝ u) =
      euclideanBallEnergyEpsilon n R ε u := by
  rfl

private def weakEpsilonDensity (n : ℕ) (ε : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) : ℝ :=
  weakGradientSq n G x / 2 + (1 - ‖u x‖ ^ 2) ^ 2 / (4 * ε ^ 2)

theorem weakGradientSq_dilate (n : ℕ) (ε : ℝ)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) :
    weakGradientSq n (fun y => ε • G (ε • y)) x =
      ε ^ 2 * weakGradientSq n G (ε • x) := by
  have h := weakGradientSq_inwardGradient n ε⁻¹ G x
  have hfun : inwardGradient n ε⁻¹ G =
      fun y => ε • G (ε • y) := by
    funext y
    simp [inwardGradient]
  rw [hfun] at h
  simp only [inv_inv] at h
  exact h

private theorem weakEpsilonDensity_dilate (n : ℕ) (ε : ℝ)
    (hε : ε ≠ 0) (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) :
    weakGradientSq n (fun y => ε • G (ε • y)) x / 2 +
        (1 - ‖u (ε • x)‖ ^ 2) ^ 2 / 4 =
      ε ^ 2 * weakEpsilonDensity n ε u G (ε • x) := by
  rw [weakGradientSq_dilate]
  unfold weakEpsilonDensity
  field_simp [hε]

/-- Exact scaling of the distributional-gradient energy *data*.  The
derivative relation for the scaled data is a separate weak chain rule. -/
theorem weakBallEnergyEpsilon_scaling (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) :
    ε ^ n * weakBallEnergy n (R / ε)
        (fun x => u (ε • x)) (fun x => ε • G (ε • x)) =
      ε ^ 2 * weakBallEnergyEpsilon n R ε u G := by
  let B : Set (GLEuclidean n) := Metric.ball 0 (R / ε)
  let C : Set (GLEuclidean n) := Metric.ball 0 R
  have hball : ε • B = C := epsilon_smul_ball n R ε hε
  have hchange := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (GLEuclidean n))
    (fun x => ε ^ 2 * weakEpsilonDensity n ε u G x) B hε
  have hchange' :
      (∫ x in B, ε ^ 2 * weakEpsilonDensity n ε u G (ε • x)) =
        (ε ^ n)⁻¹ *
          ∫ x in C, ε ^ 2 * weakEpsilonDensity n ε u G x := by
    simpa only [hball, smul_eq_mul,
      show Module.finrank ℝ (GLEuclidean n) = n by simp] using hchange
  have hscaled :
      weakBallEnergy n (R / ε)
          (fun x => u (ε • x)) (fun x => ε • G (ε • x)) =
        (ε ^ n)⁻¹ * (ε ^ 2 * weakBallEnergyEpsilon n R ε u G) := by
    calc
      _ = ∫ x in B, ε ^ 2 * weakEpsilonDensity n ε u G (ε • x) := by
        unfold weakBallEnergy weakBallMeasure B
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        exact weakEpsilonDensity_dilate n ε hε.ne' u G x
      _ = (ε ^ n)⁻¹ * ∫ x in C,
            ε ^ 2 * weakEpsilonDensity n ε u G x := hchange'
      _ = (ε ^ n)⁻¹ * (ε ^ 2 * weakBallEnergyEpsilon n R ε u G) := by
        rw [integral_const_mul]
        rfl
  rw [hscaled]
  field_simp [pow_ne_zero n hε.ne']

theorem weakBallEnergyEpsilon_unitBall_scaling (n : ℕ)
    (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) :
    weakBallEnergyEpsilon n 1 ε u G =
      ε ^ (n - 2) * weakBallEnergy n ε⁻¹
        (fun y => u (ε • y)) (fun y => ε • G (ε • y)) := by
  have hpow : ε ^ n = ε ^ (n - 2) * ε ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  have hscale := weakBallEnergyEpsilon_scaling n 1 ε hε u G
  rw [one_div] at hscale
  have hscaled :
      ε ^ 2 * (ε ^ (n - 2) * weakBallEnergy n ε⁻¹
          (fun y => u (ε • y)) (fun y => ε • G (ε • y))) =
        ε ^ 2 * weakBallEnergyEpsilon n 1 ε u G := by
    calc
      _ = ε ^ n * weakBallEnergy n ε⁻¹
            (fun y => u (ε • y)) (fun y => ε • G (ε • y)) := by
        rw [hpow]
        ring
      _ = _ := hscale
  exact mul_left_cancel₀ (pow_ne_zero 2 hε.ne') hscaled.symm

end

end BrezisOP6
