import BrezisOP6.BallZeroModeCompletedBarrier
import BrezisOP6.SphereBridgeIntegral

/-!
# Completed finite-dimensional spherical bridge

For each of the finitely many target coordinates, the radial profile and
Picone admissibility hypotheses yield zero-mode nonnegativity through the
completed finite-ball theorem. The sharp sphere Poincaré estimate and the
proved mean-to-Picone integral identity then yield the vector bridge.
All trace and integrability interfaces remain explicit.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory
open scoped Topology

theorem vectorSphereBridge_integral_nonneg_from_profiles
    (m : ℕ) (hPoincare : SharpUnitSpherePoincare (m + 3))
    (f F y k₀ f₂ F₂ : ℝ → ℝ)
    (α β Af Bf AF BF : ℝ)
    (b db : Fin (m + 3) → ℝ → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hα : 0 < α)
    (hfTaylor : RadialOriginTaylorOn f β Af Bf R)
    (hFTaylor : RadialOriginTaylorOn F α AF BF R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hfpos : ∀ r ∈ Set.Ioc 0 R, 0 < f r)
    (hflt : ∀ r ∈ Set.Ioo 0 R, f r < 1)
    (hkcont : ContinuousOn k₀ (Set.Icc 0 R))
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hunique_origin : k₀ 0 = 1 →
      ∀ r ∈ Set.Ioc 0 R, k₀ r = 1)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Set.Icc 0 R))
    (hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Set.Icc 0 R))
    (hyFlt : ∀ r ∈ Set.Ioc 0 R, profileY F r < 1)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hF2diffAll : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r, 0 < r → y r = profileY F r)
    (hFposAll : ∀ r, 0 < r → 0 < F r)
    (hFltAll : ∀ r, 0 < r → F r < 1)
    (hFodeAll : ∀ r, 0 < r →
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hηcont : ContinuousOn (profileEta f F) (Set.Icc 0 R))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (g : ℝ → EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 3)))
    (hg : ∀ (r : ℝ) (i : Fin (m + 3)),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => (g r ω) i) 2
          (unitSphereMeasure (m + 3)))
    (dv : ℝ → Fin (m + 3) → UnitSphereL2 (m + 3))
    (hSmooth : ∀ r ∈ Set.Icc 0 R, ∀ i : Fin (m + 3),
      ContDiff ℝ 1 (fun x => (g r x) i))
    (hd : ∀ r ∈ Set.Icc 0 R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hCoeff : ∀ i : Fin (m + 3), ∀ r ∈ Set.Ioc 0 R,
      sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun s x => (g s x) i) (fun s => hg s i) r) = b i r / r)
    (hCoeffDeriv : ∀ i : Fin (m + 3), ∀ r ∈ Set.Ioc 0 R,
      sphereMeanCoefficient (m + 3) (dv r i) =
        deriv (fun s => b i s / s) r)
    (hbR : ∀ i : Fin (m + 3), b i R = 0)
    (hh : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ i : Fin (m + 3), ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (b i) (db i r) r)
    (hfluxDiff : ∀ i : Fin (m + 3), ∀ r ∈ Set.uIcc 0 R,
      DifferentiableAt ℝ (bridgeOriginFlux m f F (b i)) r)
    (hPicInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (profilePiconeDensity m f F (b i) (db i))
        MeasureTheory.volume 0 R)
    (hfluxInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (deriv (bridgeOriginFlux m f F (b i)))
        MeasureTheory.volume 0 R)
    (hfullInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s x => (g s x) i) (fun s => hg s i)
        (fun s => dv s i)) MeasureTheory.volume 0 R)
    (hmeanInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t x => (g t x) i) (fun t => hg t i) s))
        (fun s => sphereMeanCoefficient (m + 3) (dv s i)))
      MeasureTheory.volume 0 R)
    (hsq_int : ∀ i : Fin (m + 3), ∀ δ : ℝ,
      0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F (b i) (db i))
        MeasureTheory.volume δ R)
    (hpiconeFluxInt : ∀ i : Fin (m + 3), ∀ δ : ℝ,
      0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F (b i)))
        MeasureTheory.volume δ R)
    (hrem_int : ∀ i : Fin (m + 3), ∀ δ : ℝ,
      0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F (b i))
        MeasureTheory.volume δ R)
    (hbcont : ∀ i : Fin (m + 3), ContinuousAt (b i) 0) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F g hg dv r := by
  have hzero : ∀ i : Fin (m + 3),
      0 ≤ ∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F (b i) (db i) r := by
    intro i
    exact ball_zero_mode_nonnegative_with_completed_profile_barrier
      m f F y k₀ (b i) (db i) f₂ F₂ R α β Af Bf AF BF
      hR hα hfTaylor hFTaylor hFpos hfpos hflt hkcont hkevent
      hkpos hterminal hunique_origin hRatioFluxCont hSlopeFluxCont
      hyFlt hFone hF2diffAll hyDiff hyMatch hFposAll hFltAll
      hFodeAll hηcont hfDiff hFDiff hdf hdF hode_f hode_F
      (hb i) (hbR i) (hPicInt i) (hsq_int i)
      (hpiconeFluxInt i) (hrem_int i) (hbcont i)
  exact vectorSphereBridge_integral_nonneg
    m hPoincare f F b db R (le_of_lt hR) g hg dv
    hSmooth hd hCoeff hCoeffDeriv hbR hh hb hfluxDiff
    hPicInt hfluxInt hfullInt hmeanInt hzero

end

end BrezisOP6
