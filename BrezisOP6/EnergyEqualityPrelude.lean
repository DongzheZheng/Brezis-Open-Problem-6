import BrezisOP6.EnergyQuadraticIntegrability

/-!
# Vanishing components at equality

If the full bridge has nonpositive integral while its quadratic and
quartic pieces are nonnegative, both pieces vanish.  This isolates the
first equality-case deduction needed for uniqueness of the minimizer.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

theorem bridge_component_integrals_zero_of_bridge_nonpos
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hquadInt : Integrable (euclideanQuadraticBridgeDensity m f F z)
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hquarticInt : Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hquadNonneg : 0 ≤ ∫ x, euclideanQuadraticBridgeDensity m f F z x
      ∂(volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖)
    (hbridgeNonpos :
      (∫ x, bridgeEnergyDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => f ‖y‖)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2) x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R))) ≤ 0) :
    (∫ x, euclideanQuadraticBridgeDensity m f F z x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) = 0 ∧
    (∫ x, euclideanQuarticBridgeDensity m f F z x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) = 0 := by
  let μ : Measure (GLEuclidean (m + 3)) :=
    volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)
  let q := euclideanQuadraticBridgeDensity m f F z
  let t := euclideanQuarticBridgeDensity m f F z
  let b : GLEuclidean (m + 3) → ℝ :=
    bridgeEnergyDensity (m + 3)
      (fun y => f ‖y‖) (fun y => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2) (fun y => ‖y‖⁻¹ ^ 2)
  have htNonneg : 0 ≤ ∫ x, t x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact bridge_quartic_nonneg (hFnonneg x hx) (hFle x hx)
  have hsum : (∫ x, b x ∂μ) =
      (∫ x, q x ∂μ) / 2 + (∫ x, t x ∂μ) / 4 := by
    have heq : b = fun x => q x / 2 + t x / 4 := by
      funext x
      exact bridgeEnergyDensity_eq_quadratic_add_quartic m f F z x
    rw [heq, integral_add (hquadInt.div_const 2)
      (hquarticInt.div_const 4)]
    simp only [integral_div]
    rfl
  change 0 ≤ ∫ x, q x ∂μ at hquadNonneg
  change ∫ x, b x ∂μ ≤ 0 at hbridgeNonpos
  rw [hsum] at hbridgeNonpos
  constructor <;> linarith

/-- When the ordered profiles are strictly separated in the open ball,
vanishing of the quartic bridge forces the quotient to be sphere-valued
almost everywhere. -/
theorem quotient_norm_sq_one_ae_of_quartic_integral_zero
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hquarticInt : Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFlt : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, x ≠ 0 → F ‖x‖ < f ‖x‖)
    (hzero : (∫ x, euclideanQuarticBridgeDensity m f F z x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) = 0) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball
      (0 : GLEuclidean (m + 3)) R)), ‖z x‖ ^ 2 = 1 := by
  let μ : Measure (GLEuclidean (m + 3)) :=
    volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)
  let t := euclideanQuarticBridgeDensity m f F z
  letI : NeZero (m + 3) := ⟨by omega⟩
  have hne : ∀ᵐ x : GLEuclidean (m + 3)
      ∂(volume : Measure (GLEuclidean (m + 3))), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have htNonneg : 0 ≤ᵐ[μ] t := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae hne] with x hxBall hxNe
    exact bridge_quartic_nonneg
      (hFnonneg x hxBall) (le_of_lt (hFlt x hxBall hxNe))
  have htZero : t =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae htNonneg hquarticInt).mp hzero
  filter_upwards [htZero, ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae hne] with x hx0 hxBall hxNe
  by_contra hne
  have hpos := bridge_quartic_pos (hFnonneg x hxBall)
    (hFlt x hxBall hxNe) hne
  exact (ne_of_gt hpos) hx0

/-- For a continuous quotient away from the origin, the preceding a.e.
constraint holds at every punctured-ball point. -/
theorem quotient_norm_sq_one_on_punctured_of_quartic_integral_zero
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContinuousOn z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hquarticInt : Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFlt : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, x ≠ 0 → F ‖x‖ < f ‖x‖)
    (hzero : (∫ x, euclideanQuarticBridgeDensity m f F z x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) = 0) :
    ∀ x : GLEuclidean (m + 3), 0 < ‖x‖ → ‖x‖ < R →
      ‖z x‖ ^ 2 = 1 := by
  let s : Set (GLEuclidean (m + 3)) :=
    {x | 0 < ‖x‖ ∧ ‖x‖ < R}
  have hsOpen : IsOpen s :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsSub : s ⊆ Metric.ball (0 : GLEuclidean (m + 3)) R := by
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2
  have hAE := quotient_norm_sq_one_ae_of_quartic_integral_zero
    m R f F z hquarticInt hFnonneg hFlt hzero
  have hAES : (fun x : GLEuclidean (m + 3) => ‖z x‖ ^ 2) =ᵐ[
      volume.restrict s] (fun _ => (1 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset hsSub hAE
  have hEqOn : Set.EqOn
      (fun x : GLEuclidean (m + 3) => ‖z x‖ ^ 2)
      (fun _ => (1 : ℝ)) s :=
    Measure.eqOn_open_of_ae_eq hAES hsOpen (hz.norm.pow 2)
      continuousOn_const
  intro x hx hR
  exact hEqOn ⟨hx, hR⟩

end

end BrezisOP6
