import BrezisOP6.SphereBridgePolarSpatial

/-!
# A scalar spherical derivative is bounded by the full spatial gradient

The radial derivative and tangential derivative of one target coordinate
are nonnegative summands of the exact polar decomposition of the
Fréchet-gradient square.  The estimate is pointwise, so it can be
integrated without assuming cancellation of signed bridge terms.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

theorem scalarSphere_radial_angular_le_full_gradient
    (n : ℕ) (z : GLEuclidean n → GLEuclidean n)
    (r : ℝ) (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (k : Fin n)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean n))) :
    r ^ 2 *
        (deriv (fun s : ℝ => (z (s • (ω : GLEuclidean n))) k) r) ^ 2 +
      (‖fderiv ℝ
          (fun y : GLEuclidean n => (z (r • y)) k)
          (ω : GLEuclidean n)‖ ^ 2 -
        ((fderiv ℝ
          (fun y : GLEuclidean n => (z (r • y)) k)
          (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2)
      ≤ r ^ 2 * euclideanGradientSq n z
        (r • (ω : GLEuclidean n)) := by
  let A : Fin n → ℝ := fun j =>
    ‖fderiv ℝ
      (fun y : GLEuclidean n => (z (r • y)) j)
      (ω : GLEuclidean n)‖ ^ 2 -
    ((fderiv ℝ
      (fun y : GLEuclidean n => (z (r • y)) j)
      (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2
  let D : GLEuclidean n :=
    deriv (fun s : ℝ => z (s • (ω : GLEuclidean n))) r
  have hApos (j : Fin n) : 0 ≤ A j := by
    have h :=
      sphereAngularIntegrand_eq_tangent_sq n
        (fun y : GLEuclidean n => (z (r • y)) j) ω
    change A j = _ at h
    rw [h]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hDcoord (j : Fin n) :
      deriv (fun s : ℝ => (z (s • (ω : GLEuclidean n))) j) r =
        D j :=
    sphereRay_coord_deriv n z r ω j hz
  have hsum :
      r ^ 2 * euclideanGradientSq n z
        (r • (ω : GLEuclidean n)) =
      ∑ j : Fin n,
        (r ^ 2 *
          (deriv (fun s : ℝ => (z (s • (ω : GLEuclidean n))) j) r) ^ 2 +
          A j) := by
    rw [euclideanGradientSq_scaled_trace_pointwise n z r ω hz]
    rw [sphereVector_norm_sq_eq_sum_coords]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hDcoord j]
  have hterm (j : Fin n) :
      0 ≤ r ^ 2 *
          (deriv (fun s : ℝ => (z (s • (ω : GLEuclidean n))) j) r) ^ 2 +
          A j := by
    exact add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (hApos j)
  have hle : r ^ 2 *
      (deriv (fun s : ℝ => (z (s • (ω : GLEuclidean n))) k) r) ^ 2 +
      A k ≤
      ∑ j : Fin n,
        (r ^ 2 *
          (deriv (fun s : ℝ => (z (s • (ω : GLEuclidean n))) j) r) ^ 2 +
          A j) :=
    Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ k)
  exact hsum ▸ hle

/-- A weighted full-gradient bound and a weighted field bound control one
target-coordinate bridge pointwise, without cancellation among target
coordinates. -/
theorem scalarSphereBridgePointwise_abs_le_power
    (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (r : ℝ) (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (k : Fin (m + 3)) (A B C : ℝ)
    (hr : 0 < r)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean (m + 3))))
    (hd0 : 0 ≤ f r ^ 2 - F r ^ 2)
    (hdle : f r ^ 2 - F r ^ 2 ≤ f r ^ 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hG : f r ^ 2 * euclideanGradientSq (m + 3) z
        (r • (ω : GLEuclidean (m + 3))) ≤
      A + B * r⁻¹ ^ 2)
    (hZ : f r ^ 2 * ‖z (r • (ω : GLEuclidean (m + 3)))‖ ^ 2 ≤ C) :
    |scalarSphereBridgePointwise m f F
      (fun s y => (z (s • y)) k) r ω| ≤
      r ^ m * (A * r ^ 2 + B + (m + 2 : ℝ) * C) := by
  let x : GLEuclidean (m + 3) := r • (ω : GLEuclidean (m + 3))
  let d : ℝ := f r ^ 2 - F r ^ 2
  let Dr : ℝ :=
    deriv (fun s : ℝ => (z (s • (ω : GLEuclidean (m + 3)))) k) r
  let Ang : ℝ :=
    ‖fderiv ℝ
      (fun y : GLEuclidean (m + 3) => (z (r • y)) k)
      (ω : GLEuclidean (m + 3))‖ ^ 2 -
    ((fderiv ℝ
      (fun y : GLEuclidean (m + 3) => (z (r • y)) k)
      (ω : GLEuclidean (m + 3))) (ω : GLEuclidean (m + 3))) ^ 2
  let G : ℝ := euclideanGradientSq (m + 3) z x
  let Z : ℝ := ‖z x‖ ^ 2
  let zk : ℝ := (z x) k
  have hd : 0 ≤ d := hd0
  have hAng0 : 0 ≤ Ang := by
    have h :=
      sphereAngularIntegrand_eq_tangent_sq (m + 3)
        (fun y : GLEuclidean (m + 3) => (z (r • y)) k) ω
    change Ang = _ at h
    rw [h]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hGeom : r ^ 2 * Dr ^ 2 + Ang ≤ r ^ 2 * G :=
    scalarSphere_radial_angular_le_full_gradient
      (m + 3) z r ω k hz
  have hGeom0 : 0 ≤ r ^ 2 * Dr ^ 2 + Ang := by positivity
  have hG0 : 0 ≤ G := by
    unfold G euclideanGradientSq
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hZcoord : zk ^ 2 ≤ Z := by
    change ((z x) k) ^ 2 ≤ ‖z x‖ ^ 2
    rw [sphereVector_norm_sq_eq_sum_coords (m + 3) (z x)]
    exact Finset.single_le_sum
      (fun i _ => sq_nonneg ((z x) i)) (Finset.mem_univ k)
  have hWeightedGeom : d * (r ^ 2 * Dr ^ 2 + Ang) ≤
      A * r ^ 2 + B := by
    have h1 := mul_le_mul_of_nonneg_left hGeom hd0
    have h2 := mul_le_mul_of_nonneg_right hdle
      (mul_nonneg (sq_nonneg r) hG0)
    have h3 := mul_le_mul_of_nonneg_left hG (sq_nonneg r)
    have hrne : r ≠ 0 := ne_of_gt hr
    have hid : r ^ 2 * (A + B * r⁻¹ ^ 2) =
        A * r ^ 2 + B := by
      field_simp [hrne]
    rw [hid] at h3
    nlinarith [h1, h2, h3]
  have hWeightedZ : d * zk ^ 2 ≤ C := by
    have h1 := mul_le_mul_of_nonneg_left hZcoord hd0
    have h2 := mul_le_mul_of_nonneg_right hdle (sq_nonneg ‖z x‖)
    nlinarith [h1, h2, hZ]
  have hrm : 0 ≤ r ^ m := pow_nonneg hr.le _
  have hT1 : 0 ≤ r ^ m * d * (r ^ 2 * Dr ^ 2 + Ang) := by
    positivity
  have hT2 : 0 ≤ (m + 2 : ℝ) * r ^ m * d * zk ^ 2 := by
    positivity
  have hT1Bound : r ^ m * d * (r ^ 2 * Dr ^ 2 + Ang) ≤
      r ^ m * (A * r ^ 2 + B) := by
    nlinarith [mul_le_mul_of_nonneg_left hWeightedGeom hrm]
  have hT2Bound : (m + 2 : ℝ) * r ^ m * d * zk ^ 2 ≤
      r ^ m * ((m + 2 : ℝ) * C) := by
    have hcoef : 0 ≤ (m + 2 : ℝ) * r ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hWeightedZ hcoef]
  have habs : |r ^ m * d * (r ^ 2 * Dr ^ 2 + Ang) -
      (m + 2 : ℝ) * r ^ m * d * zk ^ 2| ≤
      r ^ m * d * (r ^ 2 * Dr ^ 2 + Ang) +
        (m + 2 : ℝ) * r ^ m * d * zk ^ 2 := by
    calc
      _ = |r ^ m * d * (r ^ 2 * Dr ^ 2 + Ang) +
          -((m + 2 : ℝ) * r ^ m * d * zk ^ 2)| := by ring
      _ ≤ |r ^ m * d * (r ^ 2 * Dr ^ 2 + Ang)| +
          |-((m + 2 : ℝ) * r ^ m * d * zk ^ 2)| :=
        abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg hT1, abs_neg,
        abs_of_nonneg hT2]
  have hpoint :
      scalarSphereBridgePointwise m f F
        (fun s y => (z (s • y)) k) r ω =
      r ^ m * d * (r ^ 2 * Dr ^ 2 + Ang) -
        (m + 2 : ℝ) * r ^ m * d * zk ^ 2 := by
    dsimp [scalarSphereBridgePointwise, d, Dr, Ang, zk, x]
    rw [pow_add]
    ring
  rw [hpoint]
  nlinarith [habs, hT1Bound, hT2Bound]

end

end BrezisOP6
