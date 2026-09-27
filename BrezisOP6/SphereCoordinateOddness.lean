import BrezisOP6.SphereBoundaryMeanZero

/-!
# Antipodal symmetry of the concrete polar surface measure

The surface measure used throughout the bridge proof is `volume.toSphere`.
The reflection `ω ↦ -ω` preserves this measure because it reflects each
radial sector through the origin and Lebesgue measure is reflection-invariant.
Consequently every coordinate function has zero spherical mean.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise

/-- The antipodal map on the unit sphere. -/
def unitSphereAntipodal (n : ℕ) :
    Metric.sphere (0 : GLEuclidean n) 1 →
      Metric.sphere (0 : GLEuclidean n) 1 :=
  fun ω => ⟨-ω.1, by simpa [Metric.mem_sphere] using ω.2⟩

private theorem unitSphereAntipodal_continuous (n : ℕ) :
    Continuous (unitSphereAntipodal n) := by
  exact (continuous_neg.comp continuous_subtype_val).subtype_mk
    (fun ω => by simpa [Metric.mem_sphere] using ω.2)

private theorem unitSphereAntipodal_involutive (n : ℕ) :
    Function.Involutive (unitSphereAntipodal n) := by
  intro ω
  ext
  simp [unitSphereAntipodal]

private def unitSphereAntipodalHomeomorph (n : ℕ) :
    Metric.sphere (0 : GLEuclidean n) 1 ≃ₜ
      Metric.sphere (0 : GLEuclidean n) 1 where
  toFun := unitSphereAntipodal n
  invFun := unitSphereAntipodal n
  left_inv := unitSphereAntipodal_involutive n
  right_inv := unitSphereAntipodal_involutive n
  continuous_toFun := unitSphereAntipodal_continuous n
  continuous_invFun := unitSphereAntipodal_continuous n

private def radialSector (n : ℕ)
    (s : Set (Metric.sphere (0 : GLEuclidean n) 1)) : Set (GLEuclidean n) :=
  Ioo (0 : ℝ) 1 • ((↑) '' s)

private theorem radialSector_measurable (n : ℕ)
    {s : Set (Metric.sphere (0 : GLEuclidean n) 1)}
    (hs : MeasurableSet s) : MeasurableSet (radialSector n s) := by
  let E := GLEuclidean n
  let r : Ioi (0 : ℝ) := ⟨1, by simp⟩
  have hprod : MeasurableSet (s ×ˢ Iio r) := hs.prod measurableSet_Iio
  have hpre : MeasurableSet
      ((homeomorphUnitSphereProd E) ⁻¹' (s ×ˢ Iio r)) :=
    (homeomorphUnitSphereProd E).measurable hprod
  have himage : MeasurableSet
      ((Subtype.val : ({(0 : E)}ᶜ : Set E) → E) ''
        ((homeomorphUnitSphereProd E) ⁻¹' (s ×ˢ Iio r))) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton (0 : E)).compl).measurableSet_image.mpr hpre
  have heq :
      ((Subtype.val : ({(0 : E)}ᶜ : Set E) → E) ''
        ((homeomorphUnitSphereProd E) ⁻¹' (s ×ˢ Iio r))) =
        radialSector n s := by
    unfold radialSector
    rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm,
      image_image, ← image_subtype_val_Ioi_Iio r, image2_image_left,
      image2_swap, ← image_prod]
    rfl
  rw [heq] at himage
  exact himage

private theorem radialSector_antipodal (n : ℕ)
    (s : Set (Metric.sphere (0 : GLEuclidean n) 1)) :
    radialSector n (unitSphereAntipodal n ⁻¹' s) =
      Neg.neg '' radialSector n s := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨ω, hω, rfl⟩, rfl⟩
    refine ⟨r • ((unitSphereAntipodal n ω : Metric.sphere (0 : GLEuclidean n) 1) : GLEuclidean n), ?_, ?_⟩
    · refine ⟨r, hr, (unitSphereAntipodal n ω : GLEuclidean n), ?_, rfl⟩
      exact ⟨unitSphereAntipodal n ω,
        hω, rfl⟩
    · simp [unitSphereAntipodal]
  · rintro ⟨y, ⟨r, hr, z, ⟨ω, hω, rfl⟩, rfl⟩, rfl⟩
    refine ⟨r, hr, (unitSphereAntipodal n ω : GLEuclidean n), ?_, ?_⟩
    · exact ⟨unitSphereAntipodal n ω, by simpa [unitSphereAntipodal_involutive n ω] using hω, rfl⟩
    · simp [unitSphereAntipodal]

private theorem volume_neg_image_eq (n : ℕ)
    {s : Set (GLEuclidean n)} (hs : MeasurableSet s) :
    (volume : Measure (GLEuclidean n)) (Neg.neg '' s) =
      (volume : Measure (GLEuclidean n)) s := by
  have hpre : (Neg.neg : GLEuclidean n → GLEuclidean n) ⁻¹' s =
      Neg.neg '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨-x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  calc
    _ = (Measure.map Neg.neg (volume : Measure (GLEuclidean n))) s := by
      rw [Measure.map_apply measurable_neg hs, hpre]
    _ = _ := congrArg (fun ν : Measure (GLEuclidean n) => ν s)
      (Measure.map_neg_eq_self (volume : Measure (GLEuclidean n)))

/-- Reflection through the origin preserves the concrete polar surface measure. -/
theorem unitSphereAntipodal_measurePreserving (n : ℕ) :
    MeasurePreserving (unitSphereAntipodal n)
      (unitSphereMeasure n) (unitSphereMeasure n) := by
  refine ⟨(unitSphereAntipodal_continuous n).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (unitSphereAntipodal_continuous n).measurable hs]
  change (volume.toSphere) (unitSphereAntipodal n ⁻¹' s) =
    (volume.toSphere) s
  rw [((volume : Measure (GLEuclidean n)).toSphere_apply'
    ((unitSphereAntipodal_continuous n).measurable hs)),
    ((volume : Measure (GLEuclidean n)).toSphere_apply' hs)]
  change (Module.finrank ℝ (GLEuclidean n) : ENNReal) *
      (volume : Measure (GLEuclidean n))
        (radialSector n (unitSphereAntipodal n ⁻¹' s)) =
    (Module.finrank ℝ (GLEuclidean n) : ENNReal) *
      (volume : Measure (GLEuclidean n)) (radialSector n s)
  rw [radialSector_antipodal,
    volume_neg_image_eq n (radialSector_measurable n hs)]

/-- Every coordinate of the unit-sphere identity map has zero mean. -/
theorem unitSphereCoordinateMeanZero_actual (n : ℕ) :
    UnitSphereCoordinateMeanZero n := by
  intro k
  let μ := unitSphereMeasure n
  let a := unitSphereAntipodal n
  have h := (unitSphereAntipodal_measurePreserving n).integral_comp
    (unitSphereAntipodalHomeomorph n).measurableEmbedding
    (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      ((ω : GLEuclidean n) k))
  have hneg : (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ((a ω : GLEuclidean n) k) ∂μ) =
      -∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        ((ω : GLEuclidean n) k) ∂μ := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [a, unitSphereAntipodal]
  have hzero : (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ((ω : GLEuclidean n) k) ∂μ) = 0 := by
    rw [hneg] at h
    linarith
  exact hzero

end

end BrezisOP6
