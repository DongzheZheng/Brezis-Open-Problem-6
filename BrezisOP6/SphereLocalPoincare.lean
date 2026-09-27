import BrezisOP6.SpherePuncturedAngular

/-!
# A sphere-local formulation of the sharp spectral gap

The trace of the quotient field on an interior sphere is only `C¹` in a
neighborhood of that sphere.  A spectral gap formulated for globally `C¹`
ambient extensions therefore has the wrong quantifier for the comparison.
Here the spectral input is stated on any open neighborhood of the unit
sphere, and the local regularity of the scaled trace is proved directly
from punctured-ball `C¹` regularity.  The spectral inequality itself remains
an explicitly named external input.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

/-- The sharp sphere Poincaré inequality in the regularity class actually
met by a punctured-ball quotient field.  This is the external spherical
spectral fact; the ambient scalar field need only be `C¹` on an open
neighborhood of the unit sphere. -/
def SharpUnitSpherePoincareLocal (n : ℕ) : Prop :=
  ∀ (U : Set (GLEuclidean n)) (g : GLEuclidean n → ℝ),
    IsOpen U → Metric.sphere (0 : GLEuclidean n) 1 ⊆ U →
    ContDiffOn ℝ 1 g U →
    ∀ (hg : MemLp (fun ω : Metric.sphere
        (0 : GLEuclidean n) 1 => g ω) 2 (unitSphereMeasure n)),
      ((n : ℝ) - 1) *
          ‖sphereMeanZeroPart n (unitSphereTrace n g hg)‖ ^ 2 ≤
        unitSphereAngularEnergy n g

/-- Every local spectral gap implies the old global version. -/
theorem sharpUnitSpherePoincareLocal_to_global (n : ℕ)
    (hLocal : SharpUnitSpherePoincareLocal n) :
    SharpUnitSpherePoincare n := by
  intro g hg hmem
  exact hLocal Set.univ g isOpen_univ (subset_univ _)
    hg.contDiffOn hmem

/-- The domain on which a fixed-radius scaled trace of a punctured-ball
field is `C¹`. -/
def scaledPuncturedBallDomain (n : ℕ) (R r : ℝ) :
    Set (GLEuclidean n) :=
  {y | 0 < ‖r • y‖ ∧ ‖r • y‖ < R}

theorem scaledPuncturedBallDomain_isOpen (n : ℕ) (R r : ℝ) :
    IsOpen (scaledPuncturedBallDomain n R r) := by
  have hRay : Continuous (fun y : GLEuclidean n => r • y) :=
    continuous_const_smul r
  change IsOpen {y : GLEuclidean n | 0 < ‖r • y‖ ∧ ‖r • y‖ < R}
  exact (isOpen_lt continuous_const hRay.norm).inter
    (isOpen_lt hRay.norm continuous_const)

theorem unitSphere_subset_scaledPuncturedBallDomain (n : ℕ)
    (R r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    Metric.sphere (0 : GLEuclidean n) 1 ⊆
      scaledPuncturedBallDomain n R r := by
  intro y hy
  have hnorm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
  have hscaled : ‖r • y‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hnorm]
    ring
  change 0 < ‖r • y‖ ∧ ‖r • y‖ < R
  rw [hscaled]
  exact hr

/-- A field `C¹` on the punctured ball gives a scaled field `C¹` on a
concrete open neighborhood of the unit sphere. -/
theorem scaledTrace_contDiffOn_puncturedBall (n : ℕ)
    (R r : ℝ) (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R}) :
    ContDiffOn ℝ 1 (fun y : GLEuclidean n => z (r • y))
      (scaledPuncturedBallDomain n R r) := by
  exact hz.comp (contDiff_const_smul r).contDiffOn
    (fun y hy => hy)

/-- The local spectral gap applies directly to each target coordinate of
the genuine scaled quotient field on every interior sphere. -/
theorem scaledPuncturedSphereTrace_angular_gap
    (m : ℕ) (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (R r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin (m + 3))
    (hmem : MemLp (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 =>
          (z (r • (ω : GLEuclidean (m + 3)))) k) 2
      (unitSphereMeasure (m + 3))) :
    (m + 2 : ℝ) *
      ‖sphereMeanZeroPart (m + 3)
        (unitSphereTrace (m + 3)
          (fun y : GLEuclidean (m + 3) => (z (r • y)) k)
          hmem)‖ ^ 2 ≤
      unitSphereAngularEnergy (m + 3)
        (fun y : GLEuclidean (m + 3) => (z (r • y)) k) := by
  let U := scaledPuncturedBallDomain (m + 3) R r
  have hScaled := scaledTrace_contDiffOn_puncturedBall
    (m + 3) R r z hz
  have hk : ContDiffOn ℝ 1
      (fun y : GLEuclidean (m + 3) => (z (r • y)) k) U := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hScaled
  have hgap := hLocal U
    (fun y : GLEuclidean (m + 3) => (z (r • y)) k)
    (scaledPuncturedBallDomain_isOpen (m + 3) R r)
    (unitSphere_subset_scaledPuncturedBallDomain (m + 3) R r hr)
    hk hmem
  have hcoeff : (((m + 3 : ℕ) : ℝ) - 1) = (m + 2 : ℝ) := by
    push_cast
    ring
  simpa only [hcoeff] using hgap

end

end BrezisOP6
