import BrezisOP6.SphereEqualityFiniteBall
import BrezisOP6.SphereFiniteFamilyGap
import BrezisOP6.BridgeEqualityIntegral

/-!
# Equality of one actual spherical bridge coordinate

If a coordinate bridge has zero integral while its Picone mean is
nonnegative, its positive radial mean-zero variance vanishes a.e.  The
strict interior profile gap removes the weight and yields a concrete
statement about the Fréchet-derived `L²` radial slice.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

theorem finiteBall_coordinate_bridge_zero_forces_radial_ae
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hdpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < f r ^ 2 - F r ^ 2)
    (k : Fin (m + 3))
    (hfullInt : IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k))
      volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R)
    (hmeanNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)) r)
    (hfullZero : (∫ r in (0 : ℝ)..R,
      scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k) r) = 0) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      finiteBallSphereFamilyRadialL2 (m + 3) R z hz r k =
        sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz r k) •
            unitSphereConstant (m + 3) := by
  let n := m + 3
  let e := unitSphereConstant n
  let g : ℝ → GLEuclidean n → ℝ :=
    fun s y => (finiteBallSphereFamily n R z s y) k
  let hg := fun s => finiteBallSphereFamily_memLp n R z hz s k
  let v : ℝ → UnitSphereL2 n := scalarSphereFamilyTrace n g hg
  let dv : ℝ → UnitSphereL2 n :=
    fun s => finiteBallSphereFamilyRadialL2 n R z hz s k
  let c : ℝ → ℝ := fun s => sphereMeanCoefficient n (v s)
  let dc : ℝ → ℝ := fun s => sphereMeanCoefficient n (dv s)
  let d : ℝ → ℝ := fun s => f s ^ 2 - F s ^ 2
  let angular : ℝ → ℝ := fun s => unitSphereAngularEnergy n (g s)
  have he : ‖e‖ = 1 := unitSphereConstant_norm n (by omega)
  have hv : ∀ s ∈ Icc (0 : ℝ) R,
      inner ℝ (v s - c s • e) e = 0 := by
    intro s _
    exact sphereMeanZeroPart_orthogonal n (v s) he
  have hdv : ∀ s ∈ Icc (0 : ℝ) R,
      inner ℝ (dv s - dc s • e) e = 0 := by
    intro s _
    exact sphereMeanZeroPart_orthogonal n (dv s) he
  have hgap : ∀ s ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v s - c s • e‖ ^ 2 ≤ angular s :=
    finiteBallSphereFamily_angular_gap m hLocal R hR z hz k
  have hresult := bridgeQuadratic_zero_forces_remainders_zero_ae
    m e d v dv angular c dc R hR.le he hv hdv hd hgap
    hfullInt hmeanInt hmeanNonneg hfullZero
  have hweighted : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) R)),
      s ^ (m + 2) * d s * ‖dv s - dc s • e‖ ^ 2 = 0 :=
    hresult.2.mono (fun s hs => hs.1)
  exact radial_meanZero_derivative_zero_ae_of_weighted_zero
    m e d dv dc R hdpos hweighted

end

end BrezisOP6
