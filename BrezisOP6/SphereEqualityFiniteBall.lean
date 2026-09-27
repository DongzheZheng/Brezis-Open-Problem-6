import BrezisOP6.SphereEqualityFiniteBallRadial
import BrezisOP6.SphereBoundaryMeanZero

/-!
# Pointwise equality on the actual punctured ball

This theorem finishes the Hilbert/sphere equality mechanism once the
quadratic bridge has supplied vanishing mean-zero radial derivative and
the physical quotient has a true left boundary trace.  The unit-length
condition supplied by quartic equality eliminates the remaining radial
constant modes at every positive interior radius.
-/

namespace BrezisOP6

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

theorem finiteBallSphereFamily_eq_identity_of_radial_rigidity
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hOdd : UnitSphereCoordinateMeanZero n)
    (hunit : ∀ x : GLEuclidean n,
      0 < ‖x‖ → ‖x‖ < R → ‖z x‖ ^ 2 = 1)
    (hderivZero : ∀ k : Fin n,
      ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) R)),
        finiteBallSphereFamilyRadialL2 n R z hz s k =
          sphereMeanCoefficient n
            (finiteBallSphereFamilyRadialL2 n R z hz s k) •
              unitSphereConstant n)
    (hOuterLimit : ∀ k : Fin n, Tendsto
      (fun s => sphereMeanZeroPart n
        (scalarSphereFamilyTrace n
          (fun t y => (finiteBallSphereFamily n R z t y) k)
          (fun t => finiteBallSphereFamily_memLp n R z hz t k) s))
      (𝓝[<] R)
      (𝓝 (sphereMeanZeroPart n
        (scalarSphereFamilyTrace n
          (fun t y => (finiteBallSphereFamily n R z t y) k)
          (fun t => finiteBallSphereFamily_memLp n R z hz t k) R))))
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      z (r • (ω : GLEuclidean n)) = (ω : GLEuclidean n) := by
  let g := finiteBallSphereFamily n R z
  let hg := fun s k => finiteBallSphereFamily_memLp n R z hz s k
  let v : ℝ → Fin n → UnitSphereL2 n :=
    fun s k => scalarSphereFamilyTrace n
      (fun t y => (g t y) k) (fun t => hg t k) s
  have hmeanOuter (k : Fin n) :
      sphereMeanCoefficient n (v R k) = 0 := by
    have hbR : vectorSphereRadialMean n g hg k R = 0 :=
      vectorSphereRadialMean_boundary_zero_of_identity_family
        n R hOdd g hg
        (fun ω => finiteBallSphereFamily_outer n R z ω) k
    have hcoeff := scalarSphereRadialMean_div n
      (fun s y => (g s y) k) (fun s => hg s k) R hR
    change sphereMeanCoefficient n (v R k) =
      vectorSphereRadialMean n g hg k R / R at hcoeff
    rw [hbR] at hcoeff
    simpa using hcoeff
  have hparts (k : Fin n) :
      sphereMeanZeroPart n (v r k) = v R k := by
    have h := finiteBallSphereFamily_meanZeroPart_eq_outer
      n R hR z hz k (hderivZero k) (hOuterLimit k) r hr
    change sphereMeanZeroPart n (v r k) =
      sphereMeanZeroPart n (v R k) at h
    simpa [sphereMeanZeroPart, hmeanOuter k] using h
  have hgc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g r ω) :=
    finiteBallSphereFamily_interior_continuous n R z hz r hr
  have hhc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g R ω) :=
    finiteBallSphereFamily_outer_continuous n R z
  have hunitg (ω : Metric.sphere (0 : GLEuclidean n) 1) :
      ‖g r ω‖ = 1 := by
    have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    have hxnorm : ‖r • (ω : GLEuclidean n)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
      ring
    have hs : ‖z (r • (ω : GLEuclidean n))‖ ^ 2 = 1 :=
      hunit (r • (ω : GLEuclidean n))
        (by rw [hxnorm]; exact hr.1)
        (by rw [hxnorm]; exact hr.2)
    change ‖finiteBallSphereFamily n R z r ω‖ = 1
    rw [finiteBallSphereFamily_interior n R z r hr]
    nlinarith [norm_nonneg (z (r • (ω : GLEuclidean n)))]
  have hunith (ω : Metric.sphere (0 : GLEuclidean n) 1) :
      ‖g R ω‖ = 1 := by
    change ‖finiteBallSphereFamily n R z R ω‖ = 1
    rw [finiteBallSphereFamily_outer]
    exact mem_sphere_zero_iff_norm.mp ω.property
  have heq := sphereValued_trace_eq_of_meanZeroPart_eq
    n hn (g r) (g R) (fun k => hg r k) (fun k => hg R k)
    hgc hhc hunitg hunith hmeanOuter hparts
  intro ω
  have h := heq ω
  change finiteBallSphereFamily n R z r ω =
    finiteBallSphereFamily n R z R ω at h
  rw [finiteBallSphereFamily_interior n R z r hr,
    finiteBallSphereFamily_outer] at h
  exact h

end

end BrezisOP6
