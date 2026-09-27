import BrezisOP6.SphereActualMeanNonnegative
import BrezisOP6.SphereActualPiconeFluxRegularity

/-!
# Actual zero-mode nonnegativity with automatic Picone flux regularity

For global C² radial profiles and a global C¹ numerator, strict profile
ordering makes every positive annulus regular. No integrability or flux
regularity of the test zero modes is assumed separately.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem actual_finiteBallSphere_mean_integral_nonneg_of_C2_profiles
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
    (horder : ∀ r ∈ Ioc (0 : ℝ) R, F r < f r)
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
    (hfC2 : ContDiff ℝ 2 f)
    (hFC2 : ContDiff ℝ 2 F)
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
        (m + 3) R f u (hfC2.of_le (by norm_num)) hfpos'
          huGlobal.contDiffOn
    let b : Fin (m + 3) → ℝ → ℝ :=
      fun k => vectorSphereRadialMean (m + 3)
        (finiteBallSphereFamily (m + 3) R z)
        (fun s i => finiteBallSphereFamily_memLp
          (m + 3) R z hz s i) k
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
  intro k
  have hfC1 : ContDiff ℝ 1 f := hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 F := hFC2.of_le (by norm_num)
  have hfDiff : Differentiable ℝ f :=
    fun r => hfC1.differentiable_one r
  have hFDiff : Differentiable ℝ F :=
    fun r => hFC1.differentiable_one r
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hfpos' : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s :=
    fun s hs hsR => hfpos s ⟨hs, hsR⟩
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos' huGlobal.contDiffOn
  let b : Fin (m + 3) → ℝ → ℝ :=
    fun i => vectorSphereRadialMean (m + 3)
      (finiteBallSphereFamily (m + 3) R z)
      (fun s j => finiteBallSphereFamily_memLp
        (m + 3) R z hz s j) i
  have hFluxRegular (i : Fin (m + 3)) (δ : ℝ)
      (hδ : 0 < δ) (hδR : δ ≤ R) :
      ContinuousOn (profilePiconeBoundaryFlux m f F (b i))
        (uIcc δ R) ∧
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F (b i)))
        volume δ R :=
    actual_finiteBallSphere_profilePiconeFlux_annulus_regular
      m R hR f F H u hfC2 hFC2 hHC1 huGlobal
      hFpos hfpos horder hfFactor huBoundary i δ hδ hδR
  exact actual_finiteBallSphere_mean_integral_nonneg
    m f F y k₀ f₂ F₂ H HF u R α β Af Bf AF BF
    hR hα hfTaylor hFTaylor hFpos hfpos hflt
    hkcont hkevent hkpos hterminal hRatioFluxCont hSlopeFluxCont
    hyFlt hFone hF2diffAll hyDiff hyMatch hFposAll hFltAll hFodeAll
    hηcont hfDiff hFDiff hdf hdF hode_f hode_F hScont
    hfC1 huGlobal hHC1 hHFC1 hFFactor huBoundary hH0 hfFactor hOdd
    (fun i δ hδ hδR => (hFluxRegular i δ hδ hδR).1)
    (fun i δ hδ hδR => (hFluxRegular i δ hδ hδR).2) k

end

end BrezisOP6
