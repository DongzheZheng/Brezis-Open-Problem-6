import BrezisOP6.WeakBallEnergy
import Mathlib

/-!
# Compact tests under dilation

The transformed test and its exact derivative are needed to verify that
inward dilation preserves the distributional weak-gradient identity.
-/

namespace BrezisOP6

noncomputable section

theorem C1ScalarCompactTest_comp_smul (n : ℕ)
    (φ : GLEuclidean n → ℝ) (hφ : C1ScalarCompactTest n φ)
    (a : ℝ) (ha : 0 < a) :
    C1ScalarCompactTest n (fun x => φ (a • x)) := by
  rcases hφ with ⟨hφdiff, ρ, hρ, hzero⟩
  refine ⟨hφdiff.comp (contDiff_const_smul a), ρ / a,
    div_nonneg hρ ha.le, ?_⟩
  intro x hx
  apply hzero
  have hnorm : ‖a • x‖ = a * ‖x‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  rw [hnorm]
  simpa only [mul_comm] using (div_le_iff₀ ha).1 hx

theorem scalarTest_fderiv_comp_smul (n : ℕ)
    (φ : GLEuclidean n → ℝ) (a : ℝ)
    (x : GLEuclidean n) (i : Fin n) :
    (fderiv ℝ (fun y => φ (a • y)) x)
        (EuclideanSpace.single i (1 : ℝ)) =
      a * (fderiv ℝ φ (a • x))
        (EuclideanSpace.single i (1 : ℝ)) := by
  rw [fderiv_comp_smul]
  simp

end

end BrezisOP6
