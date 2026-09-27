import BrezisOP6.SphereEqualityCoordinate
import BrezisOP6.SphereBridgeFullBallEquality

/-!
# From equality of the total bridge to radial rigidity in every coordinate

Each coordinate's Picone mean is nonnegative.  The local sharp spherical
gap then makes each coordinate bridge integral nonnegative.  Equality of
their finite sum forces every coordinate bridge to vanish and activates
the pointwise radial-variance equality theorem.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

theorem finiteBall_vector_bridge_zero_forces_radial_ae
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hdpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < f r ^ 2 - F r ^ 2)
    (hfullInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      volume 0 R)
    (hmeanInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R)
    (hmeanNonneg : ∀ k : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)) r)
    (hvectorZero : (∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r) = 0) :
    ∀ k : Fin (m + 3),
      ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
        finiteBallSphereFamilyRadialL2 (m + 3) R z hz r k =
          sphereMeanCoefficient (m + 3)
            (finiteBallSphereFamilyRadialL2 (m + 3) R z hz r k) •
              unitSphereConstant (m + 3) := by
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let Q : Fin (m + 3) → ℝ → ℝ :=
    fun k => scalarSphereBridgeDensity m f F
      (fun s y => (g s y) k) (fun s => hg s k) (fun s => dv s k)
  have hcoordinateNonneg (k : Fin (m + 3)) :
      0 ≤ ∫ r in (0 : ℝ)..R, Q k r := by
    let e := unitSphereConstant (m + 3)
    let v : ℝ → UnitSphereL2 (m + 3) :=
      scalarSphereFamilyTrace (m + 3)
        (fun s y => (g s y) k) (fun s => hg s k)
    let d : ℝ → ℝ := fun s => f s ^ 2 - F s ^ 2
    let c : ℝ → ℝ := fun s => sphereMeanCoefficient (m + 3) (v s)
    let dc : ℝ → ℝ := fun s => sphereMeanCoefficient (m + 3) (dv s k)
    let ang : ℝ → ℝ := fun s =>
      unitSphereAngularEnergy (m + 3) (fun y => (g s y) k)
    have he : ‖e‖ = 1 := unitSphereConstant_norm (m + 3) (by omega)
    have hv : ∀ s ∈ Icc (0 : ℝ) R,
        inner ℝ (v s - c s • e) e = 0 := by
      intro s _
      exact sphereMeanZeroPart_orthogonal (m + 3) (v s) he
    have hdv : ∀ s ∈ Icc (0 : ℝ) R,
        inner ℝ (dv s k - dc s • e) e = 0 := by
      intro s _
      exact sphereMeanZeroPart_orthogonal (m + 3) (dv s k) he
    have hgap : ∀ s ∈ Icc (0 : ℝ) R,
        (m + 2 : ℝ) * ‖v s - c s • e‖ ^ 2 ≤ ang s :=
      finiteBallSphereFamily_angular_gap m hLocal R hR z hz k
    exact bridgeQuadratic_integral_nonneg_of_mean_nonneg
      m e d v (fun s => dv s k) ang c dc R hR.le
      he hv hdv hd hgap (hfullInt k) (hmeanInt k)
      (hmeanNonneg k)
  have hsum : (∑ k : Fin (m + 3),
      ∫ r in (0 : ℝ)..R, Q k r) = 0 := by
    have hsumInt :
        (∫ r in (0 : ℝ)..R, ∑ k : Fin (m + 3), Q k r) =
        ∑ k : Fin (m + 3),
          ∫ r in (0 : ℝ)..R, Q k r := by
      apply intervalIntegral.integral_finset_sum
      intro k _
      exact hfullInt k
    rw [← hsumInt]
    exact hvectorZero
  have hcoordZero (k : Fin (m + 3)) :
      (∫ r in (0 : ℝ)..R, Q k r) = 0 := by
    have hle : (∫ r in (0 : ℝ)..R, Q k r) ≤
        ∑ j : Fin (m + 3),
          ∫ r in (0 : ℝ)..R, Q j r :=
      Finset.single_le_sum
        (fun j _ => hcoordinateNonneg j) (Finset.mem_univ k)
    linarith [hcoordinateNonneg k]
  intro k
  exact finiteBall_coordinate_bridge_zero_forces_radial_ae
    m f F R hR z hz hLocal hd hdpos k
    (hfullInt k) (hmeanInt k) (hmeanNonneg k) (hcoordZero k)

/-- Positivity of the actual finite-ball vector bridge from the local
spherical spectral gap and the coordinatewise Picone means.  This is the
input needed by the energy comparison theorem, while the preceding
equality theorem handles its rigidity case. -/
theorem finiteBallSphereBridge_integral_nonneg_of_mean_nonneg
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hfullInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      volume 0 R)
    (hmeanInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R)
    (hmeanNonneg : ∀ k : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)) r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r := by
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let Q : Fin (m + 3) → ℝ → ℝ :=
    fun k => scalarSphereBridgeDensity m f F
      (fun s y => (g s y) k) (fun s => hg s k) (fun s => dv s k)
  have hcoordinateNonneg (k : Fin (m + 3)) :
      0 ≤ ∫ r in (0 : ℝ)..R, Q k r := by
    let e := unitSphereConstant (m + 3)
    let v : ℝ → UnitSphereL2 (m + 3) :=
      scalarSphereFamilyTrace (m + 3)
        (fun s y => (g s y) k) (fun s => hg s k)
    let d : ℝ → ℝ := fun s => f s ^ 2 - F s ^ 2
    let c : ℝ → ℝ := fun s => sphereMeanCoefficient (m + 3) (v s)
    let dc : ℝ → ℝ := fun s => sphereMeanCoefficient (m + 3) (dv s k)
    let ang : ℝ → ℝ := fun s =>
      unitSphereAngularEnergy (m + 3) (fun y => (g s y) k)
    have he : ‖e‖ = 1 := unitSphereConstant_norm (m + 3) (by omega)
    have hv : ∀ s ∈ Icc (0 : ℝ) R,
        inner ℝ (v s - c s • e) e = 0 := by
      intro s _
      exact sphereMeanZeroPart_orthogonal (m + 3) (v s) he
    have hdv : ∀ s ∈ Icc (0 : ℝ) R,
        inner ℝ (dv s k - dc s • e) e = 0 := by
      intro s _
      exact sphereMeanZeroPart_orthogonal (m + 3) (dv s k) he
    have hgap : ∀ s ∈ Icc (0 : ℝ) R,
        (m + 2 : ℝ) * ‖v s - c s • e‖ ^ 2 ≤ ang s :=
      finiteBallSphereFamily_angular_gap m hLocal R hR z hz k
    exact bridgeQuadratic_integral_nonneg_of_mean_nonneg
      m e d v (fun s => dv s k) ang c dc R hR.le
      he hv hdv hd hgap (hfullInt k) (hmeanInt k)
      (hmeanNonneg k)
  have hsumInt :
      (∫ r in (0 : ℝ)..R, ∑ k : Fin (m + 3), Q k r) =
      ∑ k : Fin (m + 3), ∫ r in (0 : ℝ)..R, Q k r := by
    apply intervalIntegral.integral_finset_sum
    intro k _
    exact hfullInt k
  change 0 ≤ ∫ r in (0 : ℝ)..R, ∑ k : Fin (m + 3), Q k r
  rw [hsumInt]
  exact Finset.sum_nonneg (fun k _ => hcoordinateNonneg k)

end

end BrezisOP6
