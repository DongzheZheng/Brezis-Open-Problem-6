import BrezisOP6.EnergyPublishedBallInterface
import BrezisOP6.EnergyRegularNumeratorC1

/-!
# The two-profile energy bridge for an actual smooth ball competitor

The quotient `u/f` is used only away from the radial origin.  The
transformed competitor is represented everywhere by the removable `C¹`
extension of `(F/f)u`.  Its energy agrees with the formal profile product
because a single point has zero Euclidean measure.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric
open scoped Topology

noncomputable section

/-- Ball energy only sees the germ of a field inside the ball; changing
the field at the origin or anywhere outside the ball leaves both its value
and its actual Fréchet derivative unchanged almost everywhere in the ball. -/
theorem euclideanBallEnergy_eq_of_eq_off_origin_on_ball
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (u v : GLEuclidean n → GLEuclidean n)
    (h : ∀ x ∈ Metric.ball (0 : GLEuclidean n) R,
      x ≠ 0 → u x = v x) :
    euclideanBallEnergy n R u = euclideanBallEnergy n R v := by
  letI : NeZero n := ⟨by omega⟩
  have hne : ∀ᵐ x : GLEuclidean n
      ∂(volume : Measure (GLEuclidean n)), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  unfold euclideanBallEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hne,
    ae_restrict_mem measurableSet_ball] with x hx0 hxBall
  have hnear : u =ᶠ[𝓝 x] v := by
    filter_upwards [(isOpen_ball).mem_nhds hxBall,
      eventually_ne_nhds hx0] with y hyBall hy0
    exact h y hyBall hy0
  have hderiv : fderiv ℝ u x = fderiv ℝ v x := hnear.fderiv_eq
  rw [h x hxBall hx0]
  simp only [euclideanGradientSq]
  rw [hderiv]

/-- On the punctured ball, the regular quotient recovers the original
competitor exactly. -/
theorem energyQuotient_product_eq_on_ball_of_profile_pos
    (n : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r) :
    ∀ x ∈ Metric.ball (0 : GLEuclidean n) R,
      x ≠ 0 →
        f ‖x‖ • ((f ‖x‖)⁻¹ • u x) = u x := by
  intro x hxBall hx0
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hrle : ‖x‖ ≤ R := by
    have hrlt : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxBall
    exact le_of_lt hrlt
  have hfne : f ‖x‖ ≠ 0 := ne_of_gt (hfpos ‖x‖ hrpos hrle)
  simp only [smul_smul, mul_inv_cancel₀ hfne, one_smul]

/-- The corrected finite-ball bridge needs no false `C¹` assertion about
the totalized quotient at zero.  Regular radial factors and the ordinary
vortex boundary condition supply all three outer inputs: smooth
representative, unit quotient trace, and transformed vortex trace. -/
theorem euclideanBall_energy_gap_ge_bridge_of_regular_competitor
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hfData : SmoothProfileBallInteriorData m f
      (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
      R ρf Bf)
    (hFData : SmoothProfileBallInteriorData m F
      (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
      R ρF BF)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α) (hβ : 0 < β)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x) :
    (∫ x, bridgeEnergyDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => f ‖y‖)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3)
        (fun y => (f ‖y‖)⁻¹ • u y))
      (fun y => ‖(f ‖y‖)⁻¹ • u y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) ≤
      euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) f) := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  let v := energyQuotientNumerator (m + 3) f F α β u
  have hfR : f R ≠ 0 := ne_of_gt (hfpos R hR le_rfl)
  have hunit : ∀ ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1 :=
    energyQuotient_unit_trace_of_radial_boundary
      (m + 3) R hR f u hfR huBoundary
  have hHfNe : ∀ x ∈ Metric.closedBall
      (0 : GLEuclidean (m + 3)) R,
      Hf (‖x‖ ^ 2) ≠ 0 :=
    radial_factor_ne_zero_on_closedBall (m + 3) R f Hf β
      hβ hHf0 hfFactor hfpos
  have hvC1 : ContDiffOn ℝ 1 v
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R) :=
    energyQuotientNumerator_contDiffOn_of_radial_factors
      (m + 3) R f F Hf HF α β u hHf hHF
      hHf0 hHF0 hHfNe hfFactor hFFactor huC1
  have hvTrace : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      v x = radialVortex (m + 3) F x :=
    energyQuotientNumerator_boundary_trace
      (m + 3) R hR f F α β u hfR huBoundary
  have hvOff : ∀ x : GLEuclidean (m + 3), x ≠ 0 →
      v x = F ‖x‖ • z x := by
    intro x hx
    exact energyQuotientNumerator_eq_profile_quotient_off_origin
      (m + 3) f F α β u x hx
  have hbridge := euclideanBall_energy_gap_ge_bridge_of_C1_representative
    m R hR f F z v ρf Bf ρF BF
    hfData hFData hunit hPublished hvOff hvC1 hvTrace
  have huEnergy : euclideanBallEnergy (m + 3) R
      (fun x => f ‖x‖ • z x) = euclideanBallEnergy (m + 3) R u :=
    euclideanBallEnergy_eq_of_eq_off_origin_on_ball
      (m + 3) (by omega) R (fun x => f ‖x‖ • z x) u
      (energyQuotient_product_eq_on_ball_of_profile_pos
        (m + 3) R f u hfpos)
  simpa only [z, huEnergy] using hbridge

end

end BrezisOP6
