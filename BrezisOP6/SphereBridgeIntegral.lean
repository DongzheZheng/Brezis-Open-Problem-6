import BrezisOP6.SphereVectorBridge
import BrezisOP6.BridgePiconeIdentification

/-!
# Integrated spherical bridge, with the Picone mean identified

For a family of actual scalar fields on Euclidean spheres, this module
integrates the sharp angular Poincaré gap and identifies the remaining
constant harmonic by the proved radial integration-by-parts theorem
`bridgeMeanDensity_integral_eq_profilePiconeDensity`.  The remaining
nonnegative Picone integral is supplied by the finite-ball zero-mode
theorems in this project.  No equality between the mean density and Picone
integral is assumed.

The coefficient identities and integrability hypotheses are stated
explicitly: they are the analytic regularity conditions to verify for a
given smooth competitor and its radial trace.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory
open scoped Topology

/-- The radial `L²` trace of a scalar family on the unit sphere. -/
def scalarSphereFamilyTrace (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => g r ω) 2
          (unitSphereMeasure n))
    (r : ℝ) : UnitSphereL2 n :=
  unitSphereTrace n (g r) (hg r)

/-- The natural regularized spherical mean coefficient `b(r)=r c(r)` of
an actual radial `L²` family. -/
def scalarSphereRadialMean (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => g r ω) 2
          (unitSphereMeasure n))
    (r : ℝ) : ℝ :=
  r * sphereMeanCoefficient n (scalarSphereFamilyTrace n g hg r)

/-- On the punctured radius axis, the actual mean is `b/r`. -/
theorem scalarSphereRadialMean_div
    (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => g r ω) 2
          (unitSphereMeasure n))
    (r : ℝ) (hr : 0 < r) :
    sphereMeanCoefficient n (scalarSphereFamilyTrace n g hg r) =
      scalarSphereRadialMean n g hg r / r := by
  simp [scalarSphereRadialMean, (ne_of_gt hr)]

/-- `L²` differentiability of the spherical family automatically gives
the radial derivative compatibility used by the Picone bridge.  This
derives the identity locally away from zero, where `b/r=c`. -/
theorem scalarSphereRadialMean_deriv_div
    (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => g r ω) 2
          (unitSphereMeasure n))
    (dv : UnitSphereL2 n) (r : ℝ) (hr : 0 < r)
    (hvr : HasDerivAt (scalarSphereFamilyTrace n g hg) dv r) :
    sphereMeanCoefficient n dv =
      deriv (fun s => scalarSphereRadialMean n g hg s / s) r := by
  have hc := sphereMeanCoefficient_hasDerivAt n
    (scalarSphereFamilyTrace n g hg) r dv hvr
  have hnear :
      (fun s => scalarSphereRadialMean n g hg s / s) =ᶠ[𝓝 r]
        (fun s => sphereMeanCoefficient n
          (scalarSphereFamilyTrace n g hg s)) := by
    filter_upwards [eventually_ne_nhds (ne_of_gt hr)] with s hs
    simp [scalarSphereRadialMean, hs]
  exact (hc.congr_of_eventuallyEq hnear).deriv.symm

/-- The regularized mean of each target coordinate of a vector family. -/
def vectorSphereRadialMean (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ (r : ℝ) (i : Fin n),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => (g r ω) i) 2
          (unitSphereMeasure n))
    (i : Fin n) (r : ℝ) : ℝ :=
  scalarSphereRadialMean n (fun s x => (g s x) i) (fun s => hg s i) r

/-- The two mean-coefficient hypotheses in the vector bridge follow from
radial `L²` differentiability when `bᵢ(r)=r cᵢ(r)`. -/
theorem vectorSphereRadialMean_compat
    (n : ℕ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ (r : ℝ) (i : Fin n),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => (g r ω) i) 2
          (unitSphereMeasure n))
    (dv : ℝ → Fin n → UnitSphereL2 n) (R : ℝ)
    (hvr : ∀ i : Fin n, ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt
        (scalarSphereFamilyTrace n
          (fun s x => (g s x) i) (fun s => hg s i))
        (dv r i) r) :
    (∀ i : Fin n, ∀ r ∈ Set.Ioc 0 R,
      sphereMeanCoefficient n
        (scalarSphereFamilyTrace n
          (fun s x => (g s x) i) (fun s => hg s i) r) =
        vectorSphereRadialMean n g hg i r / r) ∧
    (∀ i : Fin n, ∀ r ∈ Set.Ioc 0 R,
      sphereMeanCoefficient n (dv r i) =
        deriv (fun s => vectorSphereRadialMean n g hg i s / s) r) := by
  constructor
  · intro i r hr
    exact scalarSphereRadialMean_div n
      (fun s x => (g s x) i) (fun s => hg s i) r hr.1
  · intro i r hr
    exact scalarSphereRadialMean_deriv_div n
      (fun s x => (g s x) i) (fun s => hg s i)
      (dv r i) r hr.1 (hvr i r hr)

/-- The complete quadratic bridge density for one target coordinate of
an actual spherical family. -/
def scalarSphereBridgeDensity (m : ℕ)
    (f F : ℝ → ℝ)
    (g : ℝ → EuclideanSpace ℝ (Fin (m + 3)) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => g r ω) 2
          (unitSphereMeasure (m + 3)))
    (dv : ℝ → UnitSphereL2 (m + 3)) (r : ℝ) : ℝ :=
  bridgeQuadraticDensity m (fun s => f s ^ 2 - F s ^ 2)
    (scalarSphereFamilyTrace (m + 3) g hg) dv
    (fun s => unitSphereAngularEnergy (m + 3) (g s)) r

/-- Exact one-coordinate full bridge nonnegativity.  The `hzero` input is
the conclusion furnished, for admissible coefficients, by
`ball_zero_mode_nonnegative_from_origin_taylor`; the mean-to-Picone equality
is established here by `bridgeMeanDensity_integral_eq_profilePiconeDensity`.
-/
theorem scalarSphereBridge_integral_nonneg
    (m : ℕ) (hPoincare : SharpUnitSpherePoincare (m + 3))
    (f F b db : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (g : ℝ → EuclideanSpace ℝ (Fin (m + 3)) → ℝ)
    (hg : ∀ r : ℝ,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => g r ω) 2
          (unitSphereMeasure (m + 3)))
    (dv : ℝ → UnitSphereL2 (m + 3))
    (hSmooth : ∀ r ∈ Set.Icc 0 R, ContDiff ℝ 1 (g r))
    (hd : ∀ r ∈ Set.Icc 0 R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hCoeff : ∀ r ∈ Set.Ioc 0 R,
      sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3) g hg r) = b r / r)
    (hCoeffDeriv : ∀ r ∈ Set.Ioc 0 R,
      sphereMeanCoefficient (m + 3) (dv r) =
        deriv (fun s => b s / s) r)
    (hbR : b R = 0)
    (hh : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ r ∈ Set.Ioc 0 R, HasDerivAt b (db r) r)
    (hfluxDiff : ∀ r ∈ Set.uIcc 0 R,
      DifferentiableAt ℝ (bridgeOriginFlux m f F b) r)
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
    exact sphereTrace_angular_gap m hPoincare (g r) (hSmooth r hr) (hg r)
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
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le hR]
      filter_upwards [] with r hr
      have hc : c r = b r / r := hCoeff r hr
      have hdc : dc r = deriv (fun t => b t / t) r := hCoeffDeriv r hr
      simp only [bridgeMeanDensity, hc, hdc]
    exact hcoeffIntegral.trans
      (bridgeMeanDensity_integral_eq_profilePiconeDensity
        m f F b db R hR hbR hh hb hfluxDiff hPicInt hfluxInt)
  exact bridgeQuadratic_nonnegative_of_zero_mode
    m e (fun s => f s ^ 2 - F s ^ 2) v dv angular c dc
    f F b db R hR he hd hv hdv hgap hfullInt hmeanInt
    hmeanIdent hzero

/-- The radial full-bridge density for an actual vector-valued sphere
family, obtained by summing its target-coordinate `L²` densities. -/
def vectorSphereBridgeDensity (m : ℕ) (f F : ℝ → ℝ)
    (g : ℝ → EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 3)))
    (hg : ∀ (r : ℝ) (i : Fin (m + 3)),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => (g r ω) i) 2
          (unitSphereMeasure (m + 3)))
    (dv : ℝ → Fin (m + 3) → UnitSphereL2 (m + 3))
    (r : ℝ) : ℝ :=
  ∑ i : Fin (m + 3),
    scalarSphereBridgeDensity m f F
      (fun s x => (g s x) i) (fun s => hg s i)
      (fun s => dv s i) r

/-- Summing the proved scalar full-bridge estimate over the finitely many
target coordinates gives the vector full-bridge estimate.  Every indexed
`hzero` can be obtained from the finite-ball Picone theorem for that
coordinate. -/
theorem vectorSphereBridge_integral_nonneg
    (m : ℕ) (hPoincare : SharpUnitSpherePoincare (m + 3))
    (f F : ℝ → ℝ) (b db : Fin (m + 3) → ℝ → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
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
    (hzero : ∀ i : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F (b i) (db i) r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F g hg dv r := by
  have hi (i : Fin (m + 3)) :
      0 ≤ ∫ r in (0 : ℝ)..R,
        scalarSphereBridgeDensity m f F
          (fun s x => (g s x) i) (fun s => hg s i)
          (fun s => dv s i) r :=
    scalarSphereBridge_integral_nonneg m hPoincare f F
      (b i) (db i) R hR (fun s x => (g s x) i)
      (fun s => hg s i) (fun s => dv s i)
      (fun r hr => hSmooth r hr i) hd
      (hCoeff i) (hCoeffDeriv i) (hbR i) hh
      (hb i) (hfluxDiff i) (hPicInt i) (hfluxInt i)
      (hfullInt i) (hmeanInt i) (hzero i)
  have hsum : 0 ≤ ∑ i : Fin (m + 3),
      ∫ r in (0 : ℝ)..R,
        scalarSphereBridgeDensity m f F
          (fun s x => (g s x) i) (fun s => hg s i)
          (fun s => dv s i) r :=
    Finset.sum_nonneg (fun i _ => hi i)
  have hfin :
      (∫ r in (0 : ℝ)..R,
        vectorSphereBridgeDensity m f F g hg dv r) =
      ∑ i : Fin (m + 3),
        ∫ r in (0 : ℝ)..R,
          scalarSphereBridgeDensity m f F
            (fun s x => (g s x) i) (fun s => hg s i)
            (fun s => dv s i) r := by
    simpa only [vectorSphereBridgeDensity] using
      (intervalIntegral.integral_finset_sum (s := Finset.univ)
        (f := fun i r => scalarSphereBridgeDensity m f F
          (fun s x => (g s x) i) (fun s => hg s i)
          (fun s => dv s i) r)
        (fun i _ => hfullInt i))
  rw [hfin]
  exact hsum

/-- For the canonical regularized mean `bᵢ(r)=r cᵢ(r)`, radial `L²`
differentiability supplies both coefficient identities in the vector bridge.
The remaining hypotheses are endpoint, integrability, and Picone conditions
for these actual coefficients. -/
theorem vectorSphereBridge_integral_nonneg_of_radial_L2_deriv
    (m : ℕ) (hPoincare : SharpUnitSpherePoincare (m + 3))
    (f F : ℝ → ℝ) (db : Fin (m + 3) → ℝ → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (g : ℝ → EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 3)))
    (hg : ∀ (r : ℝ) (i : Fin (m + 3)),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => (g r ω) i) 2
          (unitSphereMeasure (m + 3)))
    (dv : ℝ → Fin (m + 3) → UnitSphereL2 (m + 3))
    (hvr : ∀ i : Fin (m + 3), ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt
        (scalarSphereFamilyTrace (m + 3)
          (fun s x => (g s x) i) (fun s => hg s i))
        (dv r i) r)
    (hSmooth : ∀ r ∈ Set.Icc 0 R, ∀ i : Fin (m + 3),
      ContDiff ℝ 1 (fun x => (g r x) i))
    (hd : ∀ r ∈ Set.Icc 0 R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hbR : ∀ i : Fin (m + 3),
      vectorSphereRadialMean (m + 3) g hg i R = 0)
    (hh : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ i : Fin (m + 3), ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (vectorSphereRadialMean (m + 3) g hg i)
        (db i r) r)
    (hfluxDiff : ∀ i : Fin (m + 3), ∀ r ∈ Set.uIcc 0 R,
      DifferentiableAt ℝ
        (bridgeOriginFlux m f F
          (vectorSphereRadialMean (m + 3) g hg i)) r)
    (hPicInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (profilePiconeDensity m f F
        (vectorSphereRadialMean (m + 3) g hg i) (db i))
        MeasureTheory.volume 0 R)
    (hfluxInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (deriv (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3) g hg i)))
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
    (hzero : ∀ i : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F
        (vectorSphereRadialMean (m + 3) g hg i) (db i) r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F g hg dv r := by
  have hcompat := vectorSphereRadialMean_compat (m + 3) g hg dv R hvr
  exact vectorSphereBridge_integral_nonneg
    m hPoincare f F (vectorSphereRadialMean (m + 3) g hg)
    db R hR g hg dv hSmooth hd hcompat.1 hcompat.2
    hbR hh hb hfluxDiff hPicInt hfluxInt hfullInt hmeanInt hzero

end

end BrezisOP6
