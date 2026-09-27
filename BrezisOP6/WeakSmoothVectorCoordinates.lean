import BrezisOP6.WeakDiagonalApproximation

/-!
# Reassembling finitely many scalar mollifiers

The scalar density theorem produces one sequence for each output coordinate.
These elementary facts package that same family as a smooth vector field and
identify the actual classical derivative coordinate by coordinate.
-/

namespace BrezisOP6

open Metric MeasureTheory Function
open scoped Topology

noncomputable section

def coordinateSmoothVector {n : ℕ}
    (φ : Fin n → GLEuclidean n → ℝ)
    (x : GLEuclidean n) : GLEuclidean n :=
  ∑ j : Fin n, (φ j x) • EuclideanSpace.single j (1 : ℝ)

theorem coordinateSmoothVector_apply {n : ℕ}
    (φ : Fin n → GLEuclidean n → ℝ) (x : GLEuclidean n) (j : Fin n) :
    (coordinateSmoothVector φ x) j = φ j x := by
  classical
  simp [coordinateSmoothVector, Pi.single_apply]

theorem coordinateSmoothVector_contDiff {n : ℕ}
    (φ : Fin n → GLEuclidean n → ℝ)
    (hφ : ∀ j, ContDiff ℝ 1 (φ j)) :
    ContDiff ℝ 1 (coordinateSmoothVector φ) := by
  classical
  apply ContDiff.sum
  intro j _
  exact (hφ j).smul contDiff_const

theorem coordinateSmoothVector_zero_outside {n : ℕ} {R : ℝ}
    (φ : Fin n → GLEuclidean n → ℝ)
    (hφ : ∀ j, tsupport (φ j) ⊆ Metric.ball (0 : GLEuclidean n) R)
    (x : GLEuclidean n) (hx : R ≤ ‖x‖) :
    coordinateSmoothVector φ x = 0 := by
  classical
  have hxnot : x ∉ Metric.ball (0 : GLEuclidean n) R := by
    simpa [Metric.mem_ball, dist_zero_right] using (not_lt.mpr hx)
  have hzero (j : Fin n) : φ j x = 0 := by
    exact notMem_support.mp (fun hs => hxnot (hφ j (subset_tsupport _ hs)))
  simp [coordinateSmoothVector, hzero]

theorem coordinateSmoothVector_fderiv_apply {n : ℕ}
    (φ : Fin n → GLEuclidean n → ℝ)
    (hφ : ∀ j, ContDiff ℝ 1 (φ j))
    (x e : GLEuclidean n) (j : Fin n) :
    ((fderiv ℝ (coordinateSmoothVector φ) x) e) j =
      (fderiv ℝ (φ j) x) e := by
  classical
  have hsum : fderiv ℝ (coordinateSmoothVector φ) x =
      ∑ i : Fin n, (fderiv ℝ (φ i) x).smulRight
        (EuclideanSpace.single i (1 : ℝ)) := by
    unfold coordinateSmoothVector
    rw [fderiv_fun_sum]
    · apply Finset.sum_congr rfl
      intro i _
      exact fderiv_smul_const ((hφ i).differentiable_one x) _
    · intro i _
      exact ((hφ i).differentiable_one x).smul_const _
  rw [hsum]
  simp [Pi.single_apply]

end

end BrezisOP6
