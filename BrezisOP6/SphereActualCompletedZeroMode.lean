import BrezisOP6.BallZeroModeCompletedBarrierInterior
import BrezisOP6.SphereFiniteMeanIntegrabilityTransfer
import BrezisOP6.SphereActualMeanRightLimit
import BrezisOP6.SphereFiniteMeanDerivativeInterior
import BrezisOP6.SphereBoundaryMeanZero
import BrezisOP6.EnergyQuotientPuncturedC1
import BrezisOP6.SphereFiniteMeanNonnegative
import BrezisOP6.SphereOuterMeanFluxContinuity
import BrezisOP6.SphereActualFluxRightLimit

/-!
# Completed profile barrier applied to the actual finite-ball zero modes

The origin germ and positive-radius profile uniqueness are proved in the
profile modules.  This theorem supplies the remaining concrete endpoint
data for every spherical coordinate of the quotient of a smooth numerator
by its radial profile. The two Picone-flux conditions remain explicit;
square and remainder integrability follow from the contact identity.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem actual_finiteBallSphere_completed_zero_mode_nonnegative
    (m : ℕ) (f F y k₀ f₂ F₂ H : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r)
    (hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) R))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Icc (0 : ℝ) R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R))
    (hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Icc (0 : ℝ) R))
    (hyFlt : ∀ r ∈ Ioc (0 : ℝ) R, profileY F r < 1)
    (hFone : Tendsto F atTop (𝓝 (1 : ℝ)))
    (hF2diffAll : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r, 0 < r → y r = profileY F r)
    (hFposAll : ∀ r, 0 < r → 0 < F r)
    (hFltAll : ∀ r, 0 < r → F r < 1)
    (hFodeAll : ∀ r, 0 < r →
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hηcont : ContinuousOn (profileEta f F) (Icc (0 : ℝ) R))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hScont : Tendsto (profileContactResidual f F)
      (𝓝[<] R) (𝓝 (profileContactResidual f F R)))
    (hfC1 : ContDiff ℝ 1 f)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (huOrigin : ContinuousAt u 0)
    (hH : ContinuousAt H 0) (hH0 : H 0 ≠ 0)
    (hfFactor : ∀ s : ℝ, 0 < s → s ≤ R →
      f s = s * H (s ^ 2))
    (hOdd : UnitSphereCoordinateMeanZero (m + 3)) :
    let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
      fun x => (f ‖x‖)⁻¹ • u x
    let hfpos' : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s :=
      fun s hs hsR => hfpos s ⟨hs, hsR⟩
    let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      radialQuotient_contDiffOn_puncturedBall
        (m + 3) R f u hfC1 hfpos' huC1
    let b : Fin (m + 3) → ℝ → ℝ :=
      fun k => vectorSphereRadialMean (m + 3)
        (finiteBallSphereFamily (m + 3) R z)
        (fun s i => finiteBallSphereFamily_memLp
          (m + 3) R z hz s i) k
    (∀ k : Fin (m + 3), IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp
              (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R) →
    (∀ k : Fin (m + 3), IntervalIntegrable
      (deriv (bridgeOriginFlux m f F (b k))) volume 0 R) →
    (∀ k : Fin (m + 3), ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F (b k))
        (uIcc δ R)) →
    (∀ k : Fin (m + 3), ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F (b k)))
        volume δ R) →
    ∀ k : Fin (m + 3),
      (0 ≤ ∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F (b k) (deriv (b k)) r) ∧
      (0 ≤ ∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
          (fun s => sphereMeanCoefficient (m + 3)
            (scalarSphereFamilyTrace (m + 3)
              (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
              (fun t => finiteBallSphereFamily_memLp
                (m + 3) R z hz t k) s))
          (fun s => sphereMeanCoefficient (m + 3)
            (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)) r) := by
  dsimp only
  intro hmeanInt hfluxInt hPicFluxCont hPicFluxInt k
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hfpos' : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s :=
    fun s hs hsR => hfpos s ⟨hs, hsR⟩
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos' huC1
  let b : Fin (m + 3) → ℝ → ℝ :=
    fun i => vectorSphereRadialMean (m + 3)
      (finiteBallSphereFamily (m + 3) R z)
      (fun s j => finiteBallSphereFamily_memLp
        (m + 3) R z hz s j) i
  have hb (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (b k) (deriv (b k) r) r :=
    ((finiteBallSphereRadialMean_hasDerivAt_interior
      (m + 3) R z hz k r hr).differentiableAt).hasDerivAt
  have hbR : b k R = 0 :=
    vectorSphereRadialMean_boundary_zero_of_identity_family
      (m + 3) R hOdd
      (finiteBallSphereFamily (m + 3) R z)
      (fun s i => finiteBallSphereFamily_memLp
        (m + 3) R z hz s i)
      (fun ω => finiteBallSphereFamily_outer (m + 3) R z ω) k
  have hDint : IntervalIntegrable
      (profilePiconeDensity m f F (b k) (deriv (b k)))
      volume 0 R :=
    finiteBallSphere_profilePiconeDensity_intervalIntegrable
      m f F R hR z hz hfDiff hFDiff k (hmeanInt k) (hfluxInt k)
  have hblim : ∃ B : ℝ, Tendsto (b k) (𝓝[>] (0 : ℝ)) (𝓝 B) :=
    actual_finiteBallSphereRadialMean_right_limit
      (m + 3) R hR f H u hH hH0 huOrigin
      hfFactor hfpos' hz k
  have hzero : 0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F (b k) (deriv (b k)) r :=
    ball_zero_mode_nonnegative_with_completed_profile_barrier_interior
      m f F y k₀ (b k) (deriv (b k)) f₂ F₂ R α β Af Bf AF BF
      hR hα hfTaylor hFTaylor hFpos hfpos hflt
      hkcont hkevent hkpos hterminal hRatioFluxCont hSlopeFluxCont
      hyFlt hFone hF2diffAll hyDiff hyMatch hFposAll hFltAll hFodeAll
      hηcont hfDiff hFDiff hdf hdF hode_f hode_F hScont
      hb hbR hDint (hPicFluxCont k)
      (hPicFluxInt k) hblim
  have hFluxCont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (bridgeOriginFlux m f F (b k)) (uIcc δ R) := by
    intro δ hδ hδR
    exact actual_finiteBallSphere_bridgeOriginFlux_continuousOn
      m R hR f F u hfC1 hFDiff hfpos' huC1 huBoundary
      k δ hδ hδR
  have hFluxLim : Tendsto (bridgeOriginFlux m f F (b k))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    actual_finiteBallSphereRadialMean_flux_right_limit
      m R hR f F H u α β Af Bf AF BF
      hfTaylor hFTaylor hH hH0 huOrigin hfFactor hfpos' hz k
  exact ⟨hzero,
    finiteBallSphere_mean_integral_nonneg_rightLimit
      m f F R hR z hz hOdd hfDiff hFDiff k
      hFluxCont hFluxLim (hmeanInt k) (hfluxInt k) hzero⟩

end

end BrezisOP6
