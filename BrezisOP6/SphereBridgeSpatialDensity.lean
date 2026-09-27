import BrezisOP6.SphereL2NormIntegral
import BrezisOP6.SphereBridgeIntegral

/-!
# Spherical bridge as an actual surface integral

The Hilbert-space expression used in the finite-ball bridge is here
identified with an integral of pointwise radial and tangential derivatives
on the concrete Euclidean unit sphere.  The derivative-representation
and integrability hypotheses are explicit; the former follows from the
proved finite-ball radial `L²` trace theorem in applications.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

/-- The pointwise spherical integrand corresponding to one target
coordinate of the quadratic bridge. -/
def scalarSphereBridgePointwise (m : ℕ) (f F : ℝ → ℝ)
    (g : ℝ → GLEuclidean (m + 3) → ℝ) (r : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1) : ℝ :=
  let d := f r ^ 2 - F r ^ 2
  r ^ (m + 2) * d *
      (deriv (fun s : ℝ => g s ω) r) ^ 2 +
    r ^ m * d *
      (‖fderiv ℝ (g r) (ω : GLEuclidean (m + 3))‖ ^ 2 -
        ((fderiv ℝ (g r) (ω : GLEuclidean (m + 3)))
          (ω : GLEuclidean (m + 3))) ^ 2 -
        (m + 2 : ℝ) * (g r ω) ^ 2)

/-- The concrete `L²` bridge density is precisely the surface integral
of the corresponding pointwise radial/tangential density. -/
theorem scalarSphereBridgeDensity_eq_surface_integral
    (m : ℕ) (f F : ℝ → ℝ)
    (g : ℝ → GLEuclidean (m + 3) → ℝ)
    (hg : ∀ s : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 => g s ω) 2
        (unitSphereMeasure (m + 3)))
    (dv : ℝ → UnitSphereL2 (m + 3)) (r : ℝ)
    (hrep : dv r =ᶠ[ae (unitSphereMeasure (m + 3))]
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        deriv (fun s : ℝ => g s ω) r))
    (hDInt : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (deriv (fun s : ℝ => g s ω) r) ^ 2)
      (unitSphereMeasure (m + 3)))
    (hAngInt : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        ‖fderiv ℝ (g r) (ω : GLEuclidean (m + 3))‖ ^ 2 -
          ((fderiv ℝ (g r) (ω : GLEuclidean (m + 3)))
            (ω : GLEuclidean (m + 3))) ^ 2)
      (unitSphereMeasure (m + 3))) :
    scalarSphereBridgeDensity m f F g hg dv r =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        scalarSphereBridgePointwise m f F g r ω
          ∂(unitSphereMeasure (m + 3)) := by
  let μ := unitSphereMeasure (m + 3)
  let d := f r ^ 2 - F r ^ 2
  let D : Metric.sphere (0 : GLEuclidean (m + 3)) 1 → ℝ :=
    fun ω => (deriv (fun s : ℝ => g s ω) r) ^ 2
  let A : Metric.sphere (0 : GLEuclidean (m + 3)) 1 → ℝ :=
    fun ω => ‖fderiv ℝ (g r) (ω : GLEuclidean (m + 3))‖ ^ 2 -
      ((fderiv ℝ (g r) (ω : GLEuclidean (m + 3)))
        (ω : GLEuclidean (m + 3))) ^ 2
  let Q : Metric.sphere (0 : GLEuclidean (m + 3)) 1 → ℝ :=
    fun ω => (g r ω) ^ 2
  have hQInt : Integrable Q μ := by
    have hQNormInt : Integrable
        (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
          ‖g r ω‖ ^ 2) μ :=
      (hg r).integrable_norm_pow (p := 2) (by norm_num)
    convert hQNormInt using 1
    ext ω
    simp [Q, Real.norm_eq_abs, sq_abs]
  have hDNorm : ‖dv r‖ ^ 2 = ∫ ω, D ω ∂μ := by
    rw [unitSphereL2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [hrep] with ω hω
    exact congrArg (fun x : ℝ => x ^ 2) hω
  have hQNorm :
      ‖scalarSphereFamilyTrace (m + 3) g hg r‖ ^ 2 =
        ∫ ω, Q ω ∂μ :=
    unitSphereTrace_norm_sq_eq_integral (m + 3) (g r) (hg r)
  have hA : unitSphereAngularEnergy (m + 3) (g r) =
      ∫ ω, A ω ∂μ := rfl
  let a := r ^ (m + 2) * d
  let b := r ^ m * d
  change a * ‖dv r‖ ^ 2 +
      b * (unitSphereAngularEnergy (m + 3) (g r) -
        (m + 2 : ℝ) *
          ‖scalarSphereFamilyTrace (m + 3) g hg r‖ ^ 2) = _
  rw [hDNorm, hQNorm, hA]
  have hDA : Integrable (fun ω => a * D ω) μ := hDInt.const_mul _
  have hAQ : Integrable
      (fun ω => b * (A ω - (m + 2 : ℝ) * Q ω)) μ :=
    (hAngInt.sub (hQInt.const_mul _)).const_mul _
  change a * (∫ ω, D ω ∂μ) +
    b * ((∫ ω, A ω ∂μ) -
      (m + 2 : ℝ) * (∫ ω, Q ω ∂μ)) =
    ∫ ω, a * D ω + b * (A ω - (m + 2 : ℝ) * Q ω) ∂μ
  rw [integral_add hDA hAQ, integral_const_mul, integral_const_mul,
    integral_sub hAngInt (hQInt.const_mul _), integral_const_mul]

/-- Target-coordinate summation for an arbitrary radius-indexed vector
family.  This form applies to the explicit finite-ball family, whose
values at radii outside `(0,R)` are chosen only for `L²` membership. -/
theorem vectorSphereBridgeDensity_eq_surface_integral_general
    (m : ℕ) (f F : ℝ → ℝ)
    (g : ℝ → GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hg : ∀ (s : ℝ) (k : Fin (m + 3)),
      MemLp (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 => (g s ω) k) 2
        (unitSphereMeasure (m + 3)))
    (dv : ℝ → Fin (m + 3) → UnitSphereL2 (m + 3))
    (r : ℝ)
    (hrep : ∀ k : Fin (m + 3),
      dv r k =ᶠ[ae (unitSphereMeasure (m + 3))]
        (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
          deriv (fun s : ℝ => (g s ω) k) r))
    (hDInt : ∀ k : Fin (m + 3), Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (deriv (fun s : ℝ => (g s ω) k) r) ^ 2)
      (unitSphereMeasure (m + 3)))
    (hAngInt : ∀ k : Fin (m + 3), Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        ‖fderiv ℝ (fun y : GLEuclidean (m + 3) => (g r y) k)
            (ω : GLEuclidean (m + 3))‖ ^ 2 -
          ((fderiv ℝ
            (fun y : GLEuclidean (m + 3) => (g r y) k)
            (ω : GLEuclidean (m + 3)))
            (ω : GLEuclidean (m + 3))) ^ 2)
      (unitSphereMeasure (m + 3)))
    (hPointInt : ∀ k : Fin (m + 3), Integrable
      (scalarSphereBridgePointwise m f F
        (fun s y => (g s y) k) r)
      (unitSphereMeasure (m + 3))) :
    vectorSphereBridgeDensity m f F g hg dv r =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        (∑ k : Fin (m + 3),
          scalarSphereBridgePointwise m f F
            (fun s y => (g s y) k) r ω)
          ∂(unitSphereMeasure (m + 3)) := by
  unfold vectorSphereBridgeDensity
  calc
    (∑ k : Fin (m + 3),
      scalarSphereBridgeDensity m f F
        (fun s y => (g s y) k) (fun s => hg s k)
        (fun s => dv s k) r) =
      ∑ k : Fin (m + 3),
        ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
          scalarSphereBridgePointwise m f F
            (fun s y => (g s y) k) r ω
            ∂(unitSphereMeasure (m + 3)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact scalarSphereBridgeDensity_eq_surface_integral m f F
        (fun s y => (g s y) k) (fun s => hg s k)
        (fun s => dv s k) r (hrep k) (hDInt k) (hAngInt k)
    _ = _ := by
      rw [integral_finset_sum]
      intro k _
      exact hPointInt k

end

end BrezisOP6
