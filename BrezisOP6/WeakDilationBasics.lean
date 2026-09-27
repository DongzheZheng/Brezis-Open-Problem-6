import BrezisOP6.EnergyIBP
import Mathlib

/-!
# Exact integral behavior under inward dilation

These lemmas are the measure-theoretic first step of simultaneous
`H¹ ∩ L⁴` approximation.  They apply to whole-space zero extensions.  They
do not assert strong convergence or weak-derivative compatibility.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- Pull a whole-space field inward by the factor `a>0`. -/
def inwardDilation (n : ℕ) (a : ℝ)
    (w : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n) :
    GLEuclidean n := w (a⁻¹ • x)

/-- Inward dilation preserves global square-integrability. -/
theorem inwardDilation_norm_sq_integrable (n : ℕ) (a : ℝ)
    (ha : 0 < a) (w : GLEuclidean n → GLEuclidean n)
    (hw : Integrable (fun x => ‖w x‖ ^ 2) volume) :
    Integrable (fun x => ‖inwardDilation n a w x‖ ^ 2) volume := by
  exact hw.comp_smul (inv_ne_zero ha.ne')

/-- Inward dilation preserves global fourth-power integrability. -/
theorem inwardDilation_norm_four_integrable (n : ℕ) (a : ℝ)
    (ha : 0 < a) (w : GLEuclidean n → GLEuclidean n)
    (hw : Integrable (fun x => ‖w x‖ ^ 4) volume) :
    Integrable (fun x => ‖inwardDilation n a w x‖ ^ 4) volume := by
  exact hw.comp_smul (inv_ne_zero ha.ne')

/-- Exact square-integral Jacobian under inward dilation. -/
theorem inwardDilation_norm_sq_integral (n : ℕ) (a : ℝ)
    (ha : 0 < a) (w : GLEuclidean n → GLEuclidean n) :
    (∫ x, ‖inwardDilation n a w x‖ ^ 2) =
      a ^ n * ∫ x, ‖w x‖ ^ 2 := by
  simpa only [inwardDilation, smul_eq_mul,
    show Module.finrank ℝ (GLEuclidean n) = n by simp] using
    (Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure (GLEuclidean n))
      (fun x => ‖w x‖ ^ 2) ha.le)

/-- Exact fourth-power integral Jacobian under inward dilation. -/
theorem inwardDilation_norm_four_integral (n : ℕ) (a : ℝ)
    (ha : 0 < a) (w : GLEuclidean n → GLEuclidean n) :
    (∫ x, ‖inwardDilation n a w x‖ ^ 4) =
      a ^ n * ∫ x, ‖w x‖ ^ 4 := by
  simpa only [inwardDilation, smul_eq_mul,
    show Module.finrank ℝ (GLEuclidean n) = n by simp] using
    (Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure (GLEuclidean n))
      (fun x => ‖w x‖ ^ 4) ha.le)

/-- A zero extension supported in the closed radius-`R` ball moves into
the closed radius-`a R` ball. -/
theorem inwardDilation_zero_outside (n : ℕ) (R a : ℝ)
    (ha : 0 < a) (w : GLEuclidean n → GLEuclidean n)
    (hw : ∀ x, R ≤ ‖x‖ → w x = 0)
    (x : GLEuclidean n) (hx : a * R ≤ ‖x‖) :
    inwardDilation n a w x = 0 := by
  apply hw
  have hinv : 0 < a⁻¹ := inv_pos.mpr ha
  have hnorm : ‖a⁻¹ • x‖ = a⁻¹ * ‖x‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
  rw [hnorm]
  have hscaled : R ≤ ‖x‖ * a⁻¹ :=
    (le_mul_inv_iff₀ ha).2 (by simpa only [mul_comm] using hx)
  simpa only [mul_comm] using hscaled

end

end BrezisOP6
