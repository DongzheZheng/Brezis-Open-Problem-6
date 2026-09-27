import BrezisOP6.SphereActualCompletedZeroMode
import BrezisOP6.SphereActualMeanIntegrable
import BrezisOP6.SphereActualFluxIntegrable

/-!
# Actual zero-mode nonnegativity without mean integrability hypotheses

For a globally C¹ numerator and C¹ radial factors, the mean-density and
origin-flux integrability are consequences of the removable regularized
spherical mean. The Picone annular square and remainder integrability have
already been eliminated by the nonnegative contact decomposition.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem actual_finiteBallSphere_mean_integral_nonneg
    (m : ℕ) (f F y k₀ f₂ F₂ H HF : ℝ → ℝ)
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
    (huGlobal : ContDiff ℝ 1 u)
    (hHC1 : ContDiff ℝ 1 H) (hHFC1 : ContDiff ℝ 1 HF)
    (hFFactor : ∀ s : ℝ, 0 < s → s ≤ R →
      F s = s * HF (s ^ 2))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hH0 : H 0 ≠ 0)
    (hfFactor : ∀ s : ℝ, 0 < s → s ≤ R →
      f s = s * H (s ^ 2))
    (hOdd : UnitSphereCoordinateMeanZero (m + 3)) :
    let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
      fun x => (f ‖x‖)⁻¹ • u x
    let hfpos' : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s :=
      fun s hs hsR => hfpos s ⟨hs, hsR⟩
    let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      radialQuotient_contDiffOn_puncturedBall
        (m + 3) R f u hfC1 hfpos' huGlobal.contDiffOn
    let b : Fin (m + 3) → ℝ → ℝ :=
      fun k => vectorSphereRadialMean (m + 3)
        (finiteBallSphereFamily (m + 3) R z)
        (fun s i => finiteBallSphereFamily_memLp
          (m + 3) R z hz s i) k
    (∀ k : Fin (m + 3), ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F (b k))
        (uIcc δ R)) →
    (∀ k : Fin (m + 3), ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F (b k)))
        volume δ R) →
    ∀ k : Fin (m + 3),
      0 ≤ ∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
          (fun s => sphereMeanCoefficient (m + 3)
            (scalarSphereFamilyTrace (m + 3)
              (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
              (fun t => finiteBallSphereFamily_memLp
                (m + 3) R z hz t k) s))
          (fun s => sphereMeanCoefficient (m + 3)
            (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)) r := by
  dsimp only
  intro hPicFluxCont hPicFluxInt k
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hfpos' : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s :=
    fun s hs hsR => hfpos s ⟨hs, hsR⟩
  have huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R) :=
    huGlobal.contDiffOn
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos' huC1
  let b : Fin (m + 3) → ℝ → ℝ :=
    fun i => vectorSphereRadialMean (m + 3)
      (finiteBallSphereFamily (m + 3) R z)
      (fun s j => finiteBallSphereFamily_memLp
        (m + 3) R z hz s j) i
  have hmeanInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) i)
            (fun t => finiteBallSphereFamily_memLp
              (m + 3) R z hz t i) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s i)))
      volume 0 R := by
    intro i
    exact actual_finiteBallSphere_meanDensity_intervalIntegrable
      m R hR f F H HF u hfC1 hHC1 hHFC1 huGlobal hH0
      hfFactor hFFactor hfpos' i
  have hfluxInt : ∀ i : Fin (m + 3),
      IntervalIntegrable (deriv (bridgeOriginFlux m f F (b i)))
        volume 0 R := by
    intro i
    exact actual_finiteBallSphere_bridgeOriginFlux_deriv_intervalIntegrable
      m R hR f F H HF u hfC1 hHC1 hHFC1 huGlobal hH0
      hfFactor hFFactor hfpos' i
  exact (actual_finiteBallSphere_completed_zero_mode_nonnegative
    m f F y k₀ f₂ F₂ H u R α β Af Bf AF BF
    hR hα hfTaylor hFTaylor hFpos hfpos hflt
    hkcont hkevent hkpos hterminal hRatioFluxCont hSlopeFluxCont
    hyFlt hFone hF2diffAll hyDiff hyMatch hFposAll hFltAll hFodeAll
    hηcont hfDiff hFDiff hdf hdF hode_f hode_F hScont
    hfC1 huC1 huBoundary huGlobal.continuous.continuousAt
    hHC1.continuous.continuousAt hH0 hfFactor hOdd
    hmeanInt hfluxInt hPicFluxCont hPicFluxInt k).2

end

end BrezisOP6
