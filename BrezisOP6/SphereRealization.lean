import BrezisOP6.BridgeDecomposition
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The constant mode on a concrete Euclidean sphere

This module puts the abstract Hilbert-space decomposition of
`BridgeDecomposition` on the actual unit sphere in `EuclideanSpace ℝ (Fin n)`.
The measure is the polar-coordinate surface measure `volume.toSphere` from
mathlib.  In particular, the coefficient of the normalized constant mode is
the normalized spherical integral.  Differentiation of a radial family
commutes with taking this coefficient whenever the family has a derivative
in the sphere's real `L²` space.

The sharp sphere Poincaré estimate is deliberately displayed as a geometric
input: mathlib v4.29 does not contain the spectral theorem for the spherical
Laplacian.  No nonnegativity of the energy bridge is assumed.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

/-- The usual polar-coordinate surface measure on the Euclidean unit sphere. -/
def unitSphereMeasure (n : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  MeasureTheory.volume.toSphere

instance (n : ℕ) : IsFiniteMeasure (unitSphereMeasure n) := by
  unfold unitSphereMeasure
  infer_instance

/-- Real square-integrable functions on the Euclidean unit sphere. -/
abbrev UnitSphereL2 (n : ℕ) := Lp ℝ 2 (unitSphereMeasure n)

private def unnormalizedConstant {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] : Lp ℝ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (by finiteness) (1 : ℝ)

/-- The constant spherical harmonic normalized to `L²` norm one. -/
def unitSphereConstant (n : ℕ) : UnitSphereL2 n :=
  ‖unnormalizedConstant (unitSphereMeasure n)‖⁻¹ •
    unnormalizedConstant (unitSphereMeasure n)

/-- The surface measure is nonzero whenever the ambient dimension is positive. -/
theorem unitSphereMeasure_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    unitSphereMeasure n ≠ 0 := by
  letI : NeZero n := ⟨by omega⟩
  simpa only [unitSphereMeasure] using
    (MeasureTheory.Measure.toSphere_ne_zero
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n)))))

/-- The constant harmonic really has norm one for every positive dimension. -/
theorem unitSphereConstant_norm (n : ℕ) (hn : 1 ≤ n) :
    ‖unitSphereConstant n‖ = 1 := by
  let μ := unitSphereMeasure n
  let c := unnormalizedConstant μ
  haveI : NeZero μ := ⟨unitSphereMeasure_ne_zero n hn⟩
  have hμ : 0 < μ.real Set.univ := measureReal_univ_pos
  have hcnorm : ‖c‖ = μ.real Set.univ ^ (1 / (2 : ℝ)) := by
    change ‖indicatorConstLp 2 MeasurableSet.univ (by finiteness) (1 : ℝ)‖ = _
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num
  have hcpos : 0 < ‖c‖ := by rw [hcnorm]; positivity
  simp [unitSphereConstant, μ, c, norm_smul, hcpos.ne']

/-- The coefficient of the normalized constant harmonic. -/
def sphereMeanCoefficient (n : ℕ) (v : UnitSphereL2 n) : ℝ :=
  inner ℝ v (unitSphereConstant n)

/-- The coefficient is the spherical integral divided by the norm of the
unnormalized constant function. -/
theorem sphereMeanCoefficient_eq_integral (n : ℕ) (v : UnitSphereL2 n) :
    sphereMeanCoefficient n v =
      ‖unnormalizedConstant (unitSphereMeasure n)‖⁻¹ *
        ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          v ω ∂(unitSphereMeasure n) := by
  let μ := unitSphereMeasure n
  let c := unnormalizedConstant μ
  have hc : inner ℝ c v = ∫ ω : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1, v ω ∂μ := by
    change inner ℝ (indicatorConstLp 2 MeasurableSet.univ
      (by finiteness) (1 : ℝ)) v = _
    simpa using (L2.inner_indicatorConstLp_one
      (μ := μ) (s := Set.univ) MeasurableSet.univ (by finiteness) v)
  change inner ℝ v (‖c‖⁻¹ • c) = _
  rw [real_inner_smul_right, real_inner_comm c v, hc]

/-- The mean-zero part of a sphere field. -/
def sphereMeanZeroPart (n : ℕ) (v : UnitSphereL2 n) : UnitSphereL2 n :=
  v - sphereMeanCoefficient n v • unitSphereConstant n

/-- The projection onto the constant harmonic commutes with any radial
derivative taken in the real `L²` norm. -/
theorem sphereMeanCoefficient_hasDerivAt
    (n : ℕ) (v : ℝ → UnitSphereL2 n) (r : ℝ)
    (dv : UnitSphereL2 n) (hv : HasDerivAt v dv r) :
    HasDerivAt (fun s => sphereMeanCoefficient n (v s))
      (sphereMeanCoefficient n dv) r := by
  simpa [sphereMeanCoefficient] using
    (hv.inner ℝ (hasDerivAt_const r (unitSphereConstant n)))

/-- Once a normalized constant harmonic is available, subtracting its
coefficient gives an orthogonal mean-zero field. -/
theorem sphereMeanZeroPart_orthogonal
    (n : ℕ) (v : UnitSphereL2 n)
    (he : ‖unitSphereConstant n‖ = 1) :
    inner ℝ (sphereMeanZeroPart n v) (unitSphereConstant n) = 0 := by
  simp [sphereMeanZeroPart, sphereMeanCoefficient,
    inner_sub_left, real_inner_smul_left, he]

/-- The real `L²` norm splits into spherical mean and mean-zero variance. -/
theorem sphereNorm_sq_eq_mean_sq_add_variance
    (n : ℕ) (v : UnitSphereL2 n)
    (he : ‖unitSphereConstant n‖ = 1) :
    ‖v‖ ^ 2 = (sphereMeanCoefficient n v) ^ 2 +
      ‖sphereMeanZeroPart n v‖ ^ 2 := by
  exact norm_sq_eq_mean_sq_add_orthogonal
    (unitSphereConstant n) v (sphereMeanCoefficient n v)
    he (sphereMeanZeroPart_orthogonal n v he)

/-- Restriction of an ambient scalar field to the unit sphere, viewed in
the concrete real `L²` space. -/
def unitSphereTrace (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : MemLp (fun ω : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 => g ω) 2
        (unitSphereMeasure n)) : UnitSphereL2 n :=
  hg.toLp (fun ω => g ω)

/-- The angular Dirichlet energy of an ambient differentiable extension.
The expression subtracts the squared normal derivative from the full
Euclidean derivative.  Thus its integrand is the squared tangential
gradient on the unit sphere. -/
def unitSphereAngularEnergy (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    (‖fderiv ℝ g (ω : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
      (fderiv ℝ g (ω : EuclideanSpace ℝ (Fin n)))
        (ω : EuclideanSpace ℝ (Fin n)) ^ 2) ∂(unitSphereMeasure n)

/-- The sharp Poincaré inequality on the *actual* Euclidean unit sphere.
This is the one external spectral fact needed by the sphere bridge.  The
statement uses the concrete polar surface measure and the tangential
Dirichlet form, rather than postulating positivity of the bridge. -/
def SharpUnitSpherePoincare (n : ℕ) : Prop :=
  ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ 1 g →
    ∀ (hg : MemLp (fun ω : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 => g ω) 2
        (unitSphereMeasure n)),
      ((n : ℝ) - 1) *
          ‖sphereMeanZeroPart n (unitSphereTrace n g hg)‖ ^ 2 ≤
        unitSphereAngularEnergy n g

/-- For a sphere of dimension `m+2`, the geometric Poincaré estimate
supplies exactly the coefficient occurring in the bridge. -/
theorem sphereTrace_angular_gap
    (m : ℕ) (hPoincare : SharpUnitSpherePoincare (m + 3))
    (g : EuclideanSpace ℝ (Fin (m + 3)) → ℝ)
    (hSmooth : ContDiff ℝ 1 g)
    (hg : MemLp (fun ω : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => g ω) 2
        (unitSphereMeasure (m + 3))) :
    (m + 2 : ℝ) *
        ‖sphereMeanZeroPart (m + 3) (unitSphereTrace (m + 3) g hg)‖ ^ 2 ≤
      unitSphereAngularEnergy (m + 3) g := by
  have hcoeff : ((m + 3 : ℕ) : ℝ) - 1 = (m + 2 : ℝ) := by
    push_cast
    ring
  simpa only [hcoeff] using hPoincare g hSmooth hg

/-- Concrete spherical slice version of the bridge: after removing the
actual normalized constant harmonic, all angular variance is nonnegative.
Its only external geometric input is the sharp sphere Poincaré inequality
stated above. -/
theorem sphereBridgeSlice_sub_mean_nonneg
    (m : ℕ) (hPoincare : SharpUnitSpherePoincare (m + 3))
    (g : EuclideanSpace ℝ (Fin (m + 3)) → ℝ)
    (hSmooth : ContDiff ℝ 1 g)
    (hg : MemLp (fun ω : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => g ω) 2
        (unitSphereMeasure (m + 3)))
    (dv : UnitSphereL2 (m + 3))
    (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    0 ≤ r ^ (m + 2) * d * ‖dv‖ ^ 2 +
        r ^ m * d *
          (unitSphereAngularEnergy (m + 3) g -
            (m + 2 : ℝ) * ‖unitSphereTrace (m + 3) g hg‖ ^ 2) -
      (r ^ (m + 2) * d *
            (sphereMeanCoefficient (m + 3) dv) ^ 2 -
        (m + 2 : ℝ) * r ^ m * d *
          (sphereMeanCoefficient (m + 3)
            (unitSphereTrace (m + 3) g hg)) ^ 2) := by
  let e := unitSphereConstant (m + 3)
  let v := unitSphereTrace (m + 3) g hg
  let c := sphereMeanCoefficient (m + 3) v
  let dc := sphereMeanCoefficient (m + 3) dv
  have he : ‖e‖ = 1 := unitSphereConstant_norm (m + 3) (by omega)
  have hv : inner ℝ (v - c • e) e = 0 :=
    sphereMeanZeroPart_orthogonal (m + 3) v he
  have hdv : inner ℝ (dv - dc • e) e = 0 :=
    sphereMeanZeroPart_orthogonal (m + 3) dv he
  have hgap : (m + 2 : ℝ) * ‖v - c • e‖ ^ 2 ≤
      unitSphereAngularEnergy (m + 3) g :=
    sphereTrace_angular_gap m hPoincare g hSmooth hg
  exact bridgeQuadraticDensity_sub_mean_nonneg m e v dv r d c dc
    (unitSphereAngularEnergy (m + 3) g) hr hd he hv hdv hgap

end

end BrezisOP6
