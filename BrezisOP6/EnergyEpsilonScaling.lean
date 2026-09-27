import BrezisOP6.EnergyIBP
import BrezisOP6.EnergyVortexPointwise
import Mathlib

/-!
# Scaling of the concrete Ginzburg--Landau ball energy

This is the change of variables for the actual Fréchet-derivative energy.
It applies directly to smooth competitors.  An `H¹` version requires a
separate weak-gradient energy and a weak chain rule.
-/

namespace BrezisOP6

open MeasureTheory Metric
open scoped Pointwise

noncomputable section

/-- The Ginzburg--Landau energy with coherence length `ε`. -/
def euclideanBallEnergyEpsilon (n : ℕ) (R ε : ℝ)
    (u : GLEuclidean n → GLEuclidean n) : ℝ :=
  ∫ x, euclideanGradientSq n u x / 2 +
      (1 - ‖u x‖ ^ 2) ^ 2 / (4 * ε ^ 2)
    ∂(volume.restrict (Metric.ball (0 : GLEuclidean n) R))

private def epsilonEnergyDensity (n : ℕ) (ε : ℝ)
    (u : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n) : ℝ :=
  euclideanGradientSq n u x / 2 +
    (1 - ‖u x‖ ^ 2) ^ 2 / (4 * ε ^ 2)

/-- The squared norm of the coordinate Fréchet derivative obeys the exact
dilation law, with no differentiability assumption because `fderiv` is
totalized and `fderiv_comp_smul` holds at every point. -/
theorem euclideanGradientSq_dilate (n : ℕ) (ε : ℝ)
    (u : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n) :
    euclideanGradientSq n (fun y => u (ε • y)) x =
      ε ^ 2 * euclideanGradientSq n u (ε • x) := by
  unfold euclideanGradientSq
  calc
    (∑ i : Fin n,
      ‖(fderiv ℝ (fun y : GLEuclidean n => u (ε • y)) x)
        (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) =
        ∑ i : Fin n,
          ε ^ 2 * ‖(fderiv ℝ u (ε • x))
            (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [fderiv_comp_smul]
      simp only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
      nlinarith [sq_abs ε]
    _ = ε ^ 2 * ∑ i : Fin n,
          ‖(fderiv ℝ u (ε • x))
            (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem epsilonEnergyDensity_dilate (n : ℕ) (ε : ℝ)
    (hε : ε ≠ 0) (u : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) :
    euclideanGradientSq n (fun y => u (ε • y)) x / 2 +
        (1 - ‖u (ε • x)‖ ^ 2) ^ 2 / 4 =
      ε ^ 2 * epsilonEnergyDensity n ε u (ε • x) := by
  rw [euclideanGradientSq_dilate]
  unfold epsilonEnergyDensity
  field_simp [hε]

/-- A positive dilation maps the smaller ball exactly onto the original
ball, including when the radius itself is nonpositive. -/
theorem epsilon_smul_ball (n : ℕ) (R ε : ℝ) (hε : 0 < ε) :
    ε • Metric.ball (0 : GLEuclidean n) (R / ε) =
      Metric.ball (0 : GLEuclidean n) R := by
  rw [_root_.smul_ball hε.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hε]
  congr 1
  field_simp [hε.ne']

/-- Genuine `ε` scaling for the concrete ball integral.  In dimension `n`,
`ε^n E₁(u(ε·);B_(R/ε)) = ε² E_ε(u;B_R)`. -/
theorem euclideanBallEnergyEpsilon_scaling (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) (u : GLEuclidean n → GLEuclidean n) :
    ε ^ n * euclideanBallEnergy n (R / ε) (fun x => u (ε • x)) =
      ε ^ 2 * euclideanBallEnergyEpsilon n R ε u := by
  let B : Set (GLEuclidean n) := Metric.ball 0 (R / ε)
  let C : Set (GLEuclidean n) := Metric.ball 0 R
  have hball : ε • B = C := epsilon_smul_ball n R ε hε
  have hchange := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (GLEuclidean n))
    (fun x => ε ^ 2 * epsilonEnergyDensity n ε u x) B hε
  have hchange' :
      (∫ x in B, ε ^ 2 * epsilonEnergyDensity n ε u (ε • x)) =
        (ε ^ n)⁻¹ *
          ∫ x in C, ε ^ 2 * epsilonEnergyDensity n ε u x := by
    simpa only [hball, smul_eq_mul, show Module.finrank ℝ (GLEuclidean n) = n by simp]
      using hchange
  have hscaled : euclideanBallEnergy n (R / ε) (fun x => u (ε • x)) =
      (ε ^ n)⁻¹ * (ε ^ 2 * euclideanBallEnergyEpsilon n R ε u) := by
    calc
      euclideanBallEnergy n (R / ε) (fun x => u (ε • x)) =
          ∫ x in B, ε ^ 2 * epsilonEnergyDensity n ε u (ε • x) := by
        unfold euclideanBallEnergy B
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        exact epsilonEnergyDensity_dilate n ε hε.ne' u x
      _ = (ε ^ n)⁻¹ * ∫ x in C,
            ε ^ 2 * epsilonEnergyDensity n ε u x := hchange'
      _ = (ε ^ n)⁻¹ * (ε ^ 2 * euclideanBallEnergyEpsilon n R ε u) := by
        rw [integral_const_mul]
        rfl
  rw [hscaled]
  field_simp [pow_ne_zero n hε.ne']

/-- The unit-ball scaling identity in the precise exponent form used in the
manuscript, for the pointwise-Fréchet energy. -/
theorem euclideanBallEnergyEpsilon_unitBall_scaling (n : ℕ)
    (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (u : GLEuclidean n → GLEuclidean n) :
    euclideanBallEnergyEpsilon n 1 ε u =
      ε ^ (n - 2) *
        euclideanBallEnergy n ε⁻¹ (fun y => u (ε • y)) := by
  have hpow : ε ^ n = ε ^ (n - 2) * ε ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  have hscale := euclideanBallEnergyEpsilon_scaling n 1 ε hε u
  rw [one_div] at hscale
  have hscaled :
      ε ^ 2 * (ε ^ (n - 2) *
        euclideanBallEnergy n ε⁻¹ (fun y => u (ε • y))) =
        ε ^ 2 * euclideanBallEnergyEpsilon n 1 ε u := by
    calc
      _ = ε ^ n * euclideanBallEnergy n ε⁻¹ (fun y => u (ε • y)) := by
        rw [hpow]
        ring
      _ = _ := hscale
  exact mul_left_cancel₀ (pow_ne_zero 2 hε.ne') hscaled.symm

/-- A comparison for the rescaled unit-coherence energy is exactly a
comparison for the original `ε`-energy. -/
theorem euclideanBallEnergyEpsilon_le_iff_dilate (n : ℕ) (R ε : ℝ)
    (hε : 0 < ε) (u v : GLEuclidean n → GLEuclidean n) :
    euclideanBallEnergyEpsilon n R ε u ≤
        euclideanBallEnergyEpsilon n R ε v ↔
      euclideanBallEnergy n (R / ε) (fun x => u (ε • x)) ≤
        euclideanBallEnergy n (R / ε) (fun x => v (ε • x)) := by
  have hu := euclideanBallEnergyEpsilon_scaling n R ε hε u
  have hv := euclideanBallEnergyEpsilon_scaling n R ε hε v
  constructor
  · intro h
    have hscaled := (mul_le_mul_iff_right₀ (sq_pos_of_pos hε)).2 h
    rw [← hu, ← hv] at hscaled
    exact (mul_le_mul_iff_right₀ (pow_pos hε n)).1 hscaled
  · intro h
    have hscaled := (mul_le_mul_iff_right₀ (pow_pos hε n)).2 h
    rw [hu, hv] at hscaled
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hε)).1 hscaled

/-- Dilation of a radial vortex corresponds to dilation of its scalar
profile. -/
theorem radialVortex_dilate (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (x : GLEuclidean n) :
    radialVortex n f (ε • x) =
      radialVortex n (fun r => f (ε * r)) x := by
  by_cases hx : x = 0
  · subst x
    simp [radialVortex]
  have hnorm : ‖ε • x‖ = ε * ‖x‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [radialVortex, hnorm, smul_smul]
  congr 1
  field_simp [hε.ne', hxnorm]

end

end BrezisOP6
