import BrezisOP6.SphereLocalPoincare
import BrezisOP6.SphereBridgeIntegral
import BrezisOP6.BridgePiconeIdentificationRightLimit

/-!
# Integrated spherical bridge with a one-sided origin flux

The local sphere gap and the Picone mean identity are assembled without
assuming the regularized mean or its elementary flux is continuous at the
totalized radius zero.  The flux is integrated over positive annuli and its
right limit is taken at the origin.
-/

namespace BrezisOP6

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- Integrated scalar bridge after a sharp gap has been proved for the
actual sphere slices.  In particular, no global ambient `C¹` extension of
those slices is required. -/
theorem scalarSphereBridge_integral_nonneg_of_local_gap_rightLimit
    (m : ℕ) (f F b db : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (g : ℝ → GLEuclidean (m + 3) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 => g r ω) 2
        (unitSphereMeasure (m + 3)))
    (dv : ℝ → UnitSphereL2 (m + 3))
    (hGap : ∀ r ∈ Set.Icc 0 R,
      (m + 2 : ℝ) *
        ‖sphereMeanZeroPart (m + 3)
          (scalarSphereFamilyTrace (m + 3) g hg r)‖ ^ 2 ≤
        unitSphereAngularEnergy (m + 3) (g r))
    (hd : ∀ r ∈ Set.Icc 0 R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hCoeff : ∀ r ∈ Set.Ioo 0 R,
      sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3) g hg r) = b r / r)
    (hCoeffDeriv : ∀ r ∈ Set.Ioo 0 R,
      sphereMeanCoefficient (m + 3) (dv r) =
        deriv (fun s => b s / s) r)
    (hbR : b R = 0)
    (hh : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ r ∈ Set.Ioo 0 R, HasDerivAt b (db r) r)
    (hfluxCont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (bridgeOriginFlux m f F b) (Set.uIcc δ R))
    (hfluxLim : Tendsto (bridgeOriginFlux m f F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hPicInt : IntervalIntegrable
      (profilePiconeDensity m f F b db) MeasureTheory.volume 0 R)
    (hfluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) MeasureTheory.volume 0 R)
    (hfullInt : IntervalIntegrable
      (scalarSphereBridgeDensity m f F g hg dv)
      MeasureTheory.volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3) g hg s))
        (fun s => sphereMeanCoefficient (m + 3) (dv s)))
      MeasureTheory.volume 0 R)
    (hzero : 0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      scalarSphereBridgeDensity m f F g hg dv r := by
  let e := unitSphereConstant (m + 3)
  let v := scalarSphereFamilyTrace (m + 3) g hg
  let c := fun r => sphereMeanCoefficient (m + 3) (v r)
  let dc := fun r => sphereMeanCoefficient (m + 3) (dv r)
  let angular := fun r => unitSphereAngularEnergy (m + 3) (g r)
  have he : ‖e‖ = 1 := unitSphereConstant_norm (m + 3) (by omega)
  have hv : ∀ r ∈ Set.Icc 0 R,
      inner ℝ (v r - c r • e) e = 0 := by
    intro r _
    exact sphereMeanZeroPart_orthogonal (m + 3) (v r) he
  have hdv : ∀ r ∈ Set.Icc 0 R,
      inner ℝ (dv r - dc r • e) e = 0 := by
    intro r _
    exact sphereMeanZeroPart_orthogonal (m + 3) (dv r) he
  have hgap : ∀ r ∈ Set.Icc 0 R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r := by
    intro r hr
    exact hGap r hr
  have hmeanIdent :
      (∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2) c dc r) =
      ∫ r in (0 : ℝ)..R, profilePiconeDensity m f F b db r := by
    have hcoeffIntegral :
        (∫ r in (0 : ℝ)..R,
          bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2) c dc r) =
        ∫ r in (0 : ℝ)..R,
          bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
            (fun s => b s / s)
            (fun s => deriv (fun t => b t / t) s) r := by
      apply interval_integral_congr_interior
      intro r hr
      have hr' : r ∈ Set.Ioo (0 : ℝ) R := by
        simpa [Set.uIoo_of_le hR.le] using hr
      have hc : c r = b r / r := hCoeff r hr'
      have hdc : dc r = deriv (fun t => b t / t) r :=
        hCoeffDeriv r hr'
      simp only [bridgeMeanDensity, hc, hdc]
    exact hcoeffIntegral.trans
      (bridgeMeanDensity_integral_eq_profilePiconeDensity_rightLimit
        m f F b db R hR hbR hh hb hfluxCont hfluxLim hPicInt hfluxInt)
  exact bridgeQuadratic_nonnegative_of_zero_mode
    m e (fun s => f s ^ 2 - F s ^ 2) v dv angular c dc
    f F b db R hR.le he hd hv hdv hgap hfullInt hmeanInt
    hmeanIdent hzero

/-- Coordinatewise local-gap bridge assembled into the complete vector
quadratic bridge.  The zero-mode conclusion is supplied for each target
coordinate by the interior Picone theorem. -/
theorem vectorSphereBridge_integral_nonneg_of_local_gap_rightLimit
    (m : ℕ) (f F : ℝ → ℝ)
    (b db : Fin (m + 3) → ℝ → ℝ)
    (R : ℝ) (hR : 0 < R)
    (g : ℝ → GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hg : ∀ (s : ℝ) (k : Fin (m + 3)),
      MemLp (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 => (g s ω) k) 2
        (unitSphereMeasure (m + 3)))
    (dv : ℝ → Fin (m + 3) → UnitSphereL2 (m + 3))
    (hGap : ∀ k : Fin (m + 3), ∀ r ∈ Set.Icc 0 R,
      (m + 2 : ℝ) *
        ‖sphereMeanZeroPart (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun s y => (g s y) k) (fun s => hg s k) r)‖ ^ 2 ≤
        unitSphereAngularEnergy (m + 3)
          (fun y => (g r y) k))
    (hd : ∀ r ∈ Set.Icc 0 R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hCoeff : ∀ k : Fin (m + 3), ∀ r ∈ Set.Ioo 0 R,
      sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun s y => (g s y) k) (fun s => hg s k) r) = b k r / r)
    (hCoeffDeriv : ∀ k : Fin (m + 3), ∀ r ∈ Set.Ioo 0 R,
      sphereMeanCoefficient (m + 3) (dv r k) =
        deriv (fun s => b k s / s) r)
    (hbR : ∀ k : Fin (m + 3), b k R = 0)
    (hh : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ k : Fin (m + 3), ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (b k) (db k r) r)
    (hfluxCont : ∀ k : Fin (m + 3), ∀ δ : ℝ,
      0 < δ → δ ≤ R →
      ContinuousOn (bridgeOriginFlux m f F (b k))
        (Set.uIcc δ R))
    (hfluxLim : ∀ k : Fin (m + 3),
      Tendsto (bridgeOriginFlux m f F (b k))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hPicInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (profilePiconeDensity m f F (b k) (db k))
        volume 0 R)
    (hfluxInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (deriv (bridgeOriginFlux m f F (b k))) volume 0 R)
    (hfullInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (g s y) k) (fun s => hg s k)
        (fun s => dv s k)) volume 0 R)
    (hmeanInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (g t y) k) (fun t => hg t k) s))
        (fun s => sphereMeanCoefficient (m + 3) (dv s k)))
      volume 0 R)
    (hzero : ∀ k : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F (b k) (db k) r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F g hg dv r := by
  have hi (k : Fin (m + 3)) :
      0 ≤ ∫ r in (0 : ℝ)..R,
        scalarSphereBridgeDensity m f F
          (fun s y => (g s y) k) (fun s => hg s k)
          (fun s => dv s k) r :=
    scalarSphereBridge_integral_nonneg_of_local_gap_rightLimit m f F
      (b k) (db k) R hR
      (fun s y => (g s y) k) (fun s => hg s k)
      (fun s => dv s k) (hGap k) hd
      (hCoeff k) (hCoeffDeriv k) (hbR k) hh
      (hb k) (hfluxCont k) (hfluxLim k) (hPicInt k) (hfluxInt k)
      (hfullInt k) (hmeanInt k) (hzero k)
  have hsum : 0 ≤ ∑ k : Fin (m + 3),
      ∫ r in (0 : ℝ)..R,
        scalarSphereBridgeDensity m f F
          (fun s y => (g s y) k) (fun s => hg s k)
          (fun s => dv s k) r :=
    Finset.sum_nonneg (fun k _ => hi k)
  have hfin :
      (∫ r in (0 : ℝ)..R,
        vectorSphereBridgeDensity m f F g hg dv r) =
      ∑ k : Fin (m + 3),
        ∫ r in (0 : ℝ)..R,
          scalarSphereBridgeDensity m f F
            (fun s y => (g s y) k) (fun s => hg s k)
            (fun s => dv s k) r := by
    simpa only [vectorSphereBridgeDensity] using
      (intervalIntegral.integral_finset_sum (s := Finset.univ)
        (f := fun k r => scalarSphereBridgeDensity m f F
          (fun s y => (g s y) k) (fun s => hg s k)
          (fun s => dv s k) r)
        (fun k _ => hfullInt k))
  rw [hfin]
  exact hsum

end

end BrezisOP6
