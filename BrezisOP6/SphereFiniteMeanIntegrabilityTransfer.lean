import BrezisOP6.SphereFiniteMeanDerivativeInterior
import BrezisOP6.BridgePiconeIdentificationRightLimit

/-!
# Integrability transfer from the actual spherical mean to Picone density

The regularized zero mode `b=r c` differs from the mean coefficient `c`
only by a factor of radius on the punctured ball.  The two mean-density
formulas therefore agree almost everywhere on `[0,R]`; the assignments at
the origin and outer endpoint do not alter interval integrability.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem finiteBallSphere_regularized_meanDensity_intervalIntegrable
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin (m + 3))
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp
              (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R) :
    let b := vectorSphereRadialMean (m + 3)
      (finiteBallSphereFamily (m + 3) R z)
      (fun s i => finiteBallSphereFamily_memLp
        (m + 3) R z hz s i) k
    IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => b s / s)
        (fun s => deriv (fun t => b t / t) s))
      volume 0 R := by
  dsimp only
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let b := vectorSphereRadialMean (m + 3) g hg k
  have hCoeff (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun s y => (g s y) k) (fun s => hg s k) r) =
        b r / r :=
    scalarSphereRadialMean_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k) r hr.1
  have hCoeffDeriv (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      sphereMeanCoefficient (m + 3) (dv r k) =
        deriv (fun s => b s / s) r :=
    scalarSphereRadialMean_deriv_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k)
      (dv r k) r hr.1
      (finiteBallSphereFamily_hasDerivAt_interior
        (m + 3) R z hz r hr k)
  have hRnull : ∀ᵐ r : ℝ ∂volume, r ≠ R := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      (measure_singleton R : volume {R} = 0)
  have hInterior : ∀ᵐ r : ℝ ∂volume.restrict (uIoc (0 : ℝ) R),
      r ∈ Ioo (0 : ℝ) R := by
    rw [uIoc_of_le hR.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hRnull] with r hr hrNe
    exact ⟨hr.1, lt_of_le_of_ne hr.2 hrNe⟩
  apply hmeanInt.congr_ae
  filter_upwards [hInterior] with r hr
  change bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun t y => (g t y) k) (fun t => hg t k) s))
      (fun s => sphereMeanCoefficient (m + 3) (dv s k)) r =
    bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => b s / s)
      (fun s => deriv (fun t => b t / t) s) r
  simp only [bridgeMeanDensity, hCoeff r hr,
    hCoeffDeriv r hr]

theorem finiteBallSphere_profilePiconeDensity_intervalIntegrable
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (k : Fin (m + 3))
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp
              (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R)
    (hfluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s i => finiteBallSphereFamily_memLp
            (m + 3) R z hz s i) k)))
      volume 0 R) :
    IntervalIntegrable
      (profilePiconeDensity m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s i => finiteBallSphereFamily_memLp
            (m + 3) R z hz s i) k)
        (deriv (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s i => finiteBallSphereFamily_memLp
            (m + 3) R z hz s i) k)))
      volume 0 R := by
  let b := vectorSphereRadialMean (m + 3)
    (finiteBallSphereFamily (m + 3) R z)
    (fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i) k
  let db := deriv b
  have hweight (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r := by
    have hnum : DifferentiableAt ℝ
        (fun t => f t ^ 2 - F t ^ 2) r :=
      ((hfDiff r).pow 2).sub ((hFDiff r).pow 2)
    have hden : DifferentiableAt ℝ (fun t : ℝ => t ^ 2) r :=
      differentiableAt_id.pow 2
    have hweightDiff : DifferentiableAt ℝ
        (piconeWeightFromProfiles f F) r := by
      simpa only [piconeWeightFromProfiles] using
        hnum.div hden (pow_ne_zero 2 (ne_of_gt hr.1))
    exact hweightDiff.hasDerivAt
  have hb (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      HasDerivAt b (db r) r :=
    ((finiteBallSphereRadialMean_hasDerivAt_interior
      (m + 3) R z hz k r hr).differentiableAt).hasDerivAt
  have hmeanB := finiteBallSphere_regularized_meanDensity_intervalIntegrable
    m f F R hR z hz k hmeanInt
  exact profilePiconeDensity_intervalIntegrable_of_mean_flux
    m f F b db R hR hweight hb hmeanB hfluxInt

end

end BrezisOP6
