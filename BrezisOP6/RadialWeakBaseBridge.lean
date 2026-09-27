import BrezisOP6.WeakBallClosureMain
import BrezisOP6.WeakSmoothIBPFinal
import BrezisOP6.EnergyActualFieldsIntegrable

/-!
# The manuscript's radial base field in the weak-energy semantics

On the finite ball the physical vortex `p(‖x‖) x/‖x‖` is represented by
the globally `C¹` map `H(‖x‖²) x` whenever `p(r) = r H(r²)` there.  We
construct the canonical weak-gradient field from that representative and
identify both its value and energy with the physical vortex on the ball.
No extension of the profile beyond the ball is needed for this statement.
-/

namespace BrezisOP6

open MeasureTheory Metric
open scoped Topology

noncomputable section

/-- The smooth regular-origin representative of a radial vortex. -/
def radialRegularField (n : ℕ) (H : ℝ → ℝ)
    (x : GLEuclidean n) : GLEuclidean n :=
  H (‖x‖ ^ 2) • x

theorem radialRegularField_contDiff_one
    (n : ℕ) (H : ℝ → ℝ) (hH : ContDiff ℝ 1 H) :
    ContDiff ℝ 1 (radialRegularField n H) := by
  have hsquare : ContDiff ℝ 1
      (fun x : GLEuclidean n => ‖x‖ ^ 2) :=
    contDiff_norm_sq ℝ
  exact (hH.comp hsquare).smul contDiff_id

/-- The regular representative and radial formula agree at every point of
the actual ball, including the origin. -/
theorem radialRegularField_eq_vortex_on_ball
    (n : ℕ) (R : ℝ) (p H : ℝ → ℝ)
    (hp : ∀ r : ℝ, 0 < r → r ≤ R → p r = r * H (r ^ 2)) :
    ∀ x ∈ Metric.ball (0 : GLEuclidean n) R,
      radialRegularField n H x = radialVortex n p x := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp [radialRegularField, radialVortex]
  · exact (radialVortex_eq_regular_factor_on_ball n R p H hp x hx hx0).symm

/-- The same identity also holds on the outer sphere, which is the
fixed-trace condition for every compactly supported perturbation. -/
theorem radialRegularField_eq_vortex_of_norm_le
    (n : ℕ) (R : ℝ) (p H : ℝ → ℝ)
    (hp : ∀ r : ℝ, 0 < r → r ≤ R → p r = r * H (r ^ 2))
    (x : GLEuclidean n) (hx : ‖x‖ ≤ R) :
    radialRegularField n H x = radialVortex n p x := by
  by_cases hx0 : x = 0
  · subst x
    simp [radialRegularField, radialVortex]
  · have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrne : ‖x‖ ≠ 0 := ne_of_gt hrpos
    change H (‖x‖ ^ 2) • x = (p ‖x‖ / ‖x‖) • x
    rw [hp ‖x‖ hrpos hx]
    congr 1
    field_simp [hrne]

/-- A globally `C¹` compactly supported difference produces precisely a
smooth competitor with the manuscript's prescribed outer value. -/
theorem smoothBallCompetitor_regular_add
    (m : ℕ) (R : ℝ) (p H : ℝ → ℝ)
    (hH : ContDiff ℝ 1 H)
    (hp : ∀ r : ℝ, 0 < r → r ≤ R → p r = r * H (r ^ 2))
    (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hwC1 : ContDiff ℝ 1 w)
    (hwZero : ∀ x : GLEuclidean (m + 3), R ≤ ‖x‖ → w x = 0) :
    SmoothBallCompetitor m R p
      (fun x => radialRegularField (m + 3) H x + w x) := by
  constructor
  · exact (radialRegularField_contDiff_one (m + 3) H hH).add hwC1
  · intro x hx
    change radialRegularField (m + 3) H x + w x =
      radialVortex (m + 3) p x
    rw [hwZero x hx.ge, add_zero]
    exact radialRegularField_eq_vortex_of_norm_le
      (m + 3) R p H hp x hx.le

/-- Equality on the open ball transfers the pointwise derivative and hence
the classical energy, without invoking a Sobolev approximation theorem. -/
theorem euclideanBallEnergy_eq_of_eq_on_ball
    (n : ℕ) (R : ℝ)
    (u v : GLEuclidean n → GLEuclidean n)
    (h : ∀ x ∈ Metric.ball (0 : GLEuclidean n) R, u x = v x) :
    euclideanBallEnergy n R u = euclideanBallEnergy n R v := by
  unfold euclideanBallEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hnear : u =ᶠ[𝓝 x] v := by
    filter_upwards [(isOpen_ball).mem_nhds hx] with y hy
    exact h y hy
  have hderiv : fderiv ℝ u x = fderiv ℝ v x := hnear.fderiv_eq
  simp only [euclideanGradientSq]
  rw [h x hx, hderiv]

/-- The certified weak field obtained from `H(‖x‖²)x` has exactly the
physical radial-vortex energy. -/
theorem radialRegularField_weak_energy_eq_vortex
    (n : ℕ) (R : ℝ) (p H : ℝ → ℝ)
    (hH : ContDiff ℝ 1 H)
    (hp : ∀ r : ℝ, 0 < r → r ≤ R → p r = r * H (r ^ 2)) :
    (WeakH1L4BallField.ofGlobalC1 n R
      (radialRegularField n H)
      (radialRegularField_contDiff_one n H hH)).energy =
      euclideanBallEnergy n R (radialVortex n p) := by
  rw [WeakH1L4BallField.energy]
  change weakBallEnergy n R (radialRegularField n H)
    (fderiv ℝ (radialRegularField n H)) =
      euclideanBallEnergy n R (radialVortex n p)
  rw [weakBallEnergy_classical_gradient]
  exact euclideanBallEnergy_eq_of_eq_on_ball n R
    (radialRegularField n H) (radialVortex n p)
    (radialRegularField_eq_vortex_on_ball n R p H hp)

/-- The manuscript's base vortex has a canonical certified weak-energy
representative on the ball.  The remaining premises in the conclusion are
exactly the fixed-trace density and weak equality mechanisms, not a base
field existence assumption. -/
theorem physical_weak_ball_minimum_and_ae_equality_of_regular_base
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor
      (WeakH1L4BallField.ofGlobalC1 (m + 3) R
        (radialRegularField (m + 3) p.Hf)
        (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf)))
    (hClosure : WeakSmoothFixedTraceClosure m R p.f U.field)
    (hRegularity : WeakEqualitySmoothRepresentative m R p.f
      (WeakH1L4BallField.ofGlobalC1 (m + 3) R
        (radialRegularField (m + 3) p.Hf)
        (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf))
      U.field) :
    let base := WeakH1L4BallField.ofGlobalC1 (m + 3) R
      (radialRegularField (m + 3) p.Hf)
      (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf)
    base.energy ≤ U.field.energy ∧
      (U.field.energy = base.energy →
        U.field.u =ᵐ[weakBallMeasure (m + 3) R] base.u) := by
  let base := WeakH1L4BallField.ofGlobalC1 (m + 3) R
    (radialRegularField (m + 3) p.Hf)
    (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf)
  have hBaseEnergy : base.energy =
      euclideanBallEnergy (m + 3) R
        (radialVortex (m + 3) p.f) := by
    exact radialRegularField_weak_energy_eq_vortex
      (m + 3) R p.f p.Hf p.hHf p.hfFactor
  have hBaseU : base.u =ᵐ[weakBallMeasure (m + 3) R]
      radialVortex (m + 3) p.f := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact radialRegularField_eq_vortex_on_ball
      (m + 3) R p.f p.Hf p.hfFactor x hx
  exact physical_weak_ball_minimum_and_ae_equality_of_base_energy
    m R p base hBaseEnergy hBaseU hPublished hLocal U
    hClosure hRegularity

end

end BrezisOP6
