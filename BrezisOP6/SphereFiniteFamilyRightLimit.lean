import BrezisOP6.SphereFiniteFamilyNonnegative
import BrezisOP6.SphereLocalBridgeRightLimit

/-! # Finite-ball sphere bridge with the correct origin right-limit endpoint. -/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

theorem finiteBallSphereBridge_integral_nonneg_rightLimit
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hOdd : UnitSphereCoordinateMeanZero (m + 3))
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hh : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ k : Fin (m + 3), ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k)
        (deriv (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k) r) r)
    (hfluxCont : ∀ k : Fin (m + 3), ∀ δ : ℝ,
      0 < δ → δ ≤ R → ContinuousOn
      (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k))
      (uIcc δ R))
    (hfluxLim : ∀ k : Fin (m + 3), Tendsto
      (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k))
      (𝓝[>] 0) (𝓝 0))
    (hPicInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (profilePiconeDensity m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k)
        (deriv (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k)))
        volume 0 R)
    (hfluxInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (deriv (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k)))
        volume 0 R)
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
    (hzero : ∀ k : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k)
        (deriv (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s j => finiteBallSphereFamily_memLp (m + 3) R z hz s j) k)) r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r := by
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let b : Fin (m + 3) → ℝ → ℝ :=
    fun k => vectorSphereRadialMean (m + 3) g hg k
  let db : Fin (m + 3) → ℝ → ℝ := fun k => deriv (b k)
  have hCoeff (k : Fin (m + 3)) (r : ℝ) (hr : r ∈ Ioo 0 R) :
      sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun s y => (g s y) k) (fun s => hg s k) r) = b k r / r :=
    scalarSphereRadialMean_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k) r hr.1
  have hCoeffDeriv (k : Fin (m + 3)) (r : ℝ)
      (hr : r ∈ Ioo 0 R) :
      sphereMeanCoefficient (m + 3) (dv r k) =
        deriv (fun s => b k s / s) r :=
    scalarSphereRadialMean_deriv_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k)
      (dv r k) r hr.1
      (finiteBallSphereFamily_hasDerivAt_interior
        (m + 3) R z hz r hr k)
  have hbR (k : Fin (m + 3)) : b k R = 0 :=
    vectorSphereRadialMean_boundary_zero_of_identity_family
      (m + 3) R hOdd g hg
      (fun ω => finiteBallSphereFamily_outer (m + 3) R z ω) k
  exact vectorSphereBridge_integral_nonneg_of_local_gap_rightLimit
    m f F b db R hR g hg dv
    (fun k => finiteBallSphereFamily_angular_gap
      m hLocal R hR z hz k)
    hd hCoeff hCoeffDeriv hbR hh hb hfluxCont hfluxLim
    hPicInt hfluxInt hfullInt hmeanInt hzero

end

end BrezisOP6
