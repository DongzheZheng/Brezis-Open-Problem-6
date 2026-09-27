import BrezisOP6.EnergySpatialInterface
import BrezisOP6.SphereRealization

/-!
# Euclidean radial and tangential gradient squares

This module starts with the finite-dimensional Pythagorean identity behind
the polar gradient formula.  Tangential derivatives are taken by applying
the actual Fréchet derivative to the orthogonal projections of standard
basis vectors onto the tangent hyperplane at a unit direction.  Thus the
angular term is independently defined by geometric tangential directions.
-/

namespace BrezisOP6

noncomputable section

open scoped RealInnerProductSpace

/-- Pythagoras for the rank-one radial projection of a finite family in a
real Hilbert space. -/
theorem finite_radial_tangent_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (n : ℕ) (A : Fin n → H) (u : Fin n → ℝ)
    (hu : (∑ i : Fin n, u i ^ 2) = 1) :
    (∑ i : Fin n, ‖A i‖ ^ 2) =
      ‖∑ i : Fin n, u i • A i‖ ^ 2 +
        ∑ i : Fin n,
          ‖A i - u i • (∑ j : Fin n, u j • A j)‖ ^ 2 := by
  let q : H := ∑ i : Fin n, u i • A i
  have hcross : (∑ i : Fin n, u i * inner ℝ (A i) q) = ‖q‖ ^ 2 := by
    calc
      _ = ∑ i : Fin n, inner ℝ (u i • A i) q := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_smul_left]
      _ = inner ℝ q q := by rw [← sum_inner]
      _ = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
  have hpoint (i : Fin n) :
      ‖A i - u i • q‖ ^ 2 =
        ‖A i‖ ^ 2 - 2 * u i * inner ℝ (A i) q +
          u i ^ 2 * ‖q‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  have hcrosssum :
      (∑ i : Fin n, 2 * u i * inner ℝ (A i) q) =
        2 * (∑ i : Fin n, u i * inner ℝ (A i) q) := by
    calc
      _ = ∑ i : Fin n, 2 * (u i * inner ℝ (A i) q) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hweightsum :
      (∑ i : Fin n, u i ^ 2 * ‖q‖ ^ 2) =
        (∑ i : Fin n, u i ^ 2) * ‖q‖ ^ 2 := by
    rw [Finset.sum_mul]
  have hsum :
      (∑ i : Fin n, ‖A i - u i • q‖ ^ 2) =
        (∑ i : Fin n, ‖A i‖ ^ 2) -
          2 * (∑ i : Fin n, u i * inner ℝ (A i) q) +
            (∑ i : Fin n, u i ^ 2) * ‖q‖ ^ 2 := by
    calc
      _ = ∑ i : Fin n,
            (‖A i‖ ^ 2 - 2 * u i * inner ℝ (A i) q +
              u i ^ 2 * ‖q‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hpoint i
      _ = _ := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              hcrosssum, hweightsum]
  rw [hcross, hu] at hsum
  dsimp [q] at hsum ⊢
  linarith

/-- The independent pointwise tangential squared derivative of a vector
field at the polar point `rω`, using the ambient tangent hyperplane. -/
def euclideanTangentialGradientSq (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (ω : Metric.sphere (0 : GLEuclidean n) 1) : ℝ :=
  ∑ i : Fin n,
    ‖(fderiv ℝ z x)
      (EuclideanSpace.single i (1 : ℝ) -
        ((ω : GLEuclidean n) i) • (ω : GLEuclidean n))‖ ^ 2

/-- The actual Euclidean coordinate-gradient energy splits, at every unit
direction, into the derivative along the radius and the derivatives along
the orthogonal projections of coordinate directions onto the tangent
hyperplane.  This is a pointwise Hilbert-space identity, with no PDE or
regularity hypothesis. -/
theorem euclideanGradientSq_eq_radial_add_tangent (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) :
    euclideanGradientSq n z x =
      ‖(fderiv ℝ z x) (ω : GLEuclidean n)‖ ^ 2 +
        euclideanTangentialGradientSq n z x ω := by
  let L := fderiv ℝ z x
  let w : GLEuclidean n := ω
  have hnorm : ‖w‖ = 1 := by
    simpa only [w] using (mem_sphere_zero_iff_norm.mp ω.property)
  have hsum : (∑ i : Fin n, (w i) ^ 2) = 1 := by
    calc
      (∑ i : Fin n, (w i) ^ 2) =
          ∑ i : Fin n,
            inner ℝ w ((EuclideanSpace.basisFun (Fin n) ℝ) i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [EuclideanSpace.inner_basisFun_real]
      _ = ‖w‖ ^ 2 :=
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_left w
      _ = 1 := by rw [hnorm]; norm_num
  have hrepr :
      (∑ i : Fin n, (w i) • EuclideanSpace.single i (1 : ℝ)) = w := by
    simpa only [EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w)
  have hradial :
      (∑ i : Fin n, (w i) • L (EuclideanSpace.single i (1 : ℝ))) = L w := by
    calc
      _ = L (∑ i : Fin n,
          (w i) • EuclideanSpace.single i (1 : ℝ)) := by
            simp only [map_sum, map_smul]
      _ = L w := by rw [hrepr]
  have hpyth := finite_radial_tangent_sq n
    (fun i : Fin n => L (EuclideanSpace.single i (1 : ℝ)))
    (fun i : Fin n => w i) hsum
  rw [hradial] at hpyth
  change (∑ i : Fin n,
      ‖L (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) =
    ‖L w‖ ^ 2 +
      ∑ i : Fin n,
        ‖L (EuclideanSpace.single i (1 : ℝ) - (w i) • w)‖ ^ 2
  simpa only [map_sub, map_smul] using hpyth

/-- At a unit direction, the angular-energy integrand used by the sphere
bridge is the sum of the squares of the actual derivatives along the
projected coordinate directions.  In particular, it is nonnegative
pointwise. -/
theorem sphereAngularIntegrand_eq_tangent_sq (n : ℕ)
    (g : GLEuclidean n → ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) :
    ‖fderiv ℝ g (ω : GLEuclidean n)‖ ^ 2 -
        ((fderiv ℝ g (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2 =
      ∑ i : Fin n,
        ((fderiv ℝ g (ω : GLEuclidean n))
          (EuclideanSpace.single i (1 : ℝ) -
            ((ω : GLEuclidean n) i) • (ω : GLEuclidean n))) ^ 2 := by
  let L : GLEuclidean n →L[ℝ] ℝ := fderiv ℝ g (ω : GLEuclidean n)
  let w : GLEuclidean n := ω
  have hnorm : ‖w‖ = 1 := by
    simpa only [w] using (mem_sphere_zero_iff_norm.mp ω.property)
  have hsum : (∑ i : Fin n, (w i) ^ 2) = 1 := by
    calc
      (∑ i : Fin n, (w i) ^ 2) =
          ∑ i : Fin n,
            inner ℝ w ((EuclideanSpace.basisFun (Fin n) ℝ) i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [EuclideanSpace.inner_basisFun_real]
      _ = ‖w‖ ^ 2 :=
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_left w
      _ = 1 := by rw [hnorm]; norm_num
  have hrepr :
      (∑ i : Fin n, (w i) • EuclideanSpace.single i (1 : ℝ)) = w := by
    simpa only [EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w)
  have hradial :
      (∑ i : Fin n, (w i) • L (EuclideanSpace.single i (1 : ℝ))) = L w := by
    calc
      _ = L (∑ i : Fin n,
          (w i) • EuclideanSpace.single i (1 : ℝ)) := by
            simp only [map_sum, map_smul]
      _ = L w := by rw [hrepr]
  have hdual : ‖L‖ ^ 2 =
      ∑ i : Fin n, (L (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
    simpa only [EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).norm_dual L
  have hpyth := finite_radial_tangent_sq n
    (fun i : Fin n => L (EuclideanSpace.single i (1 : ℝ)))
    (fun i : Fin n => w i) hsum
  rw [hradial] at hpyth
  have hpyth' :
      (∑ i : Fin n, (L (EuclideanSpace.single i (1 : ℝ))) ^ 2) =
        (L w) ^ 2 +
          ∑ i : Fin n,
            (L (EuclideanSpace.single i (1 : ℝ) - (w i) • w)) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs, map_sub, map_smul, smul_eq_mul]
      using hpyth
  change ‖L‖ ^ 2 - (L w) ^ 2 = _
  rw [hdual, hpyth']
  ring

end

end BrezisOP6
