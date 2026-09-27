import BrezisOP6.WeakGlobalDilationChainRule

/-!
# Transporting the weak ball theorem to the manuscript's epsilon energy

This module performs the last change of scale in the paper.  The input is
the proved weak minimum and its equality case on the ball of radius
`1 / ε` with unit coherence length.  The competitor on the unit ball is
sent to a certified competitor on that ball, including its global weak
zero trace.  The energy factor is the positive number `ε ^ (n - 2)`.
-/

namespace BrezisOP6

open MeasureTheory Metric Set
open scoped Topology

noncomputable section

/-- The epsilon-energy density of a certified `H¹ ∩ L⁴` competitor is
integrable.  Thus the real-valued energy used below is an actual finite
integral, rather than Lean's totalized value for a nonintegrable function. -/
theorem WeakH1L4BallField.epsilonEnergyDensity_integrable
    {n : ℕ} {R : ℝ} (ε : ℝ) (U : WeakH1L4BallField n R) :
    Integrable (fun x =>
      weakGradientSq n U.grad x / 2 +
        (1 - ‖U.u x‖ ^ 2) ^ 2 / (4 * ε ^ 2))
      (weakBallMeasure n R) := by
  have hone : Integrable (fun _ : GLEuclidean n => (1 : ℝ))
      (weakBallMeasure n R) := by
    change IntegrableOn (fun _ : GLEuclidean n => (1 : ℝ))
      (Metric.ball (0 : GLEuclidean n) R) volume
    exact integrableOn_const (measure_ball_ne_top)
  have hpoly : Integrable (fun x : GLEuclidean n =>
      1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4)
      (weakBallMeasure n R) :=
    (hone.sub (U.uL2.const_mul 2)).add U.uL4
  have hsource : Integrable (fun x : GLEuclidean n =>
      weakGradientSq n U.grad x / 2 +
        (1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4) / (4 * ε ^ 2))
      (weakBallMeasure n R) :=
    (U.gradL2.div_const 2).add (hpoly.div_const (4 * ε ^ 2))
  exact hsource.congr (Filter.Eventually.of_forall (fun x => by
    dsimp
    congr 1
    ring))

/-- Almost-everywhere equality on a ball survives positive dilation. -/
theorem ae_eq_on_ball_dilate (n : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (u v : GLEuclidean n → GLEuclidean n)
    (h : u =ᵐ[weakBallMeasure n R] v) :
    (fun x => u (ε • x)) =ᵐ[weakBallMeasure n (R / ε)]
      (fun x => v (ε • x)) := by
  have hVol : ∀ᵐ x ∂(volume : Measure (GLEuclidean n)),
      x ∈ Metric.ball (0 : GLEuclidean n) R → u x = v x :=
    (ae_restrict_iff' measurableSet_ball).mp h
  have hScaled :=
    (Measure.quasiMeasurePreserving_smul
      (volume : Measure (GLEuclidean n)) hε.ne').ae hVol
  apply (ae_restrict_iff' measurableSet_ball).2
  filter_upwards [hScaled] with x hx hBall
  exact hx ((ball_dilate_membership n R ε hε x).2 hBall)

/-- Almost-everywhere equality of the dilated fields pulls back to the
original ball.  This is the equality step needed after the large-ball
uniqueness theorem has been applied. -/
theorem ae_eq_on_ball_of_dilate (n : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (u v : GLEuclidean n → GLEuclidean n)
    (h : (fun y => u (ε • y)) =ᵐ[weakBallMeasure n (R / ε)]
      (fun y => v (ε • y))) :
    u =ᵐ[weakBallMeasure n R] v := by
  have hVol : ∀ᵐ y ∂(volume : Measure (GLEuclidean n)),
      y ∈ Metric.ball (0 : GLEuclidean n) (R / ε) →
        u (ε • y) = v (ε • y) :=
    (ae_restrict_iff' measurableSet_ball).mp h
  have hScaled :=
    (Measure.quasiMeasurePreserving_smul
      (volume : Measure (GLEuclidean n))
      (inv_ne_zero hε.ne')).ae hVol
  apply (ae_restrict_iff' measurableSet_ball).2
  filter_upwards [hScaled] with x hx hBall
  have hInvBall : ε⁻¹ • x ∈
      Metric.ball (0 : GLEuclidean n) (R / ε) := by
    apply (ball_dilate_membership n R ε hε (ε⁻¹ • x)).1
    simpa [smul_smul, hε.ne'] using hBall
  simpa [smul_smul, hε.ne'] using hx hInvBall

/-- The paper's `f_ε(r) = f_(1/ε)(r/ε)` makes its two radial vortex
formulas agree after the domain dilation. -/
theorem radialVortex_epsilon_dilate (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (fε fR : ℝ → ℝ)
    (hProfile : ∀ r : ℝ, fε r = fR (r / ε)) :
    (fun y => radialVortex n fε (ε • y)) = radialVortex n fR := by
  funext y
  rw [radialVortex_dilate n ε hε fε y]
  have hfun : (fun r : ℝ => fε (ε * r)) = fR := by
    funext r
    rw [hProfile]
    congr 1
    field_simp [hε.ne']
  rw [hfun]

/-- The compatibility of the paper's radial profiles also holds for the
canonical Sobolev representatives, where the vortex formula is only
required almost everywhere on the finite ball. -/
theorem WeakH1L4BallField.dilate_ae_eq_radialVortex
    {n : ℕ} (ε : ℝ) (hε : 0 < ε)
    (fε fR : ℝ → ℝ)
    (hProfile : ∀ r : ℝ, fε r = fR (r / ε))
    (base : WeakH1L4BallField n 1)
    (hBase : base.u =ᵐ[weakBallMeasure n 1] radialVortex n fε) :
    (base.dilate ε hε).u =ᵐ[weakBallMeasure n (1 / ε)]
      radialVortex n fR := by
  have hScaled := ae_eq_on_ball_dilate n 1 ε hε
    base.u (radialVortex n fε) hBase
  have hVortex := radialVortex_epsilon_dilate n ε hε fε fR hProfile
  simpa only [WeakH1L4BallField.dilate, hVortex] using hScaled

/-- Scaling for the certified weak energy of a unit-ball field, in the
exact exponent form printed in the manuscript. -/
theorem WeakH1L4BallField.unit_epsilon_energy_scaling
    {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (U : WeakH1L4BallField n 1) :
    weakBallEnergyEpsilon n 1 ε U.u U.grad =
      ε ^ (n - 2) * (U.dilate ε hε).energy := by
  change weakBallEnergyEpsilon n 1 ε U.u U.grad =
    ε ^ (n - 2) * weakBallEnergy n (1 / ε)
      (fun y => U.u (ε • y)) (fun y => ε • U.grad (ε • y))
  simpa only [one_div] using
    weakBallEnergyEpsilon_unitBall_scaling n hn ε hε U.u U.grad

/-- A unit-coherence weak theorem on the enlarged ball gives the
corresponding epsilon theorem for the *same* fixed-trace Sobolev class on
the unit ball.  In particular, the equality conclusion remains an actual
almost-everywhere equality, without a smoothness premise on the competitor.
The `hLarge` premise is precisely the arbitrary-radius theorem applied to
the dilated base field. -/
theorem weak_unit_epsilon_minimum_and_ae_equality_of_large_ball
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (base : WeakH1L4BallField n 1)
    (hLarge : ∀ V : WeakFixedTraceCompetitor (base.dilate ε hε),
      (base.dilate ε hε).energy ≤ V.field.energy ∧
        (V.field.energy = (base.dilate ε hε).energy →
          V.field.u =ᵐ[weakBallMeasure n (1 / ε)]
            (base.dilate ε hε).u))
    (U : WeakFixedTraceCompetitor base) :
    weakBallEnergyEpsilon n 1 ε base.u base.grad ≤
      weakBallEnergyEpsilon n 1 ε U.field.u U.field.grad ∧
      (weakBallEnergyEpsilon n 1 ε U.field.u U.field.grad =
          weakBallEnergyEpsilon n 1 ε base.u base.grad →
        U.field.u =ᵐ[weakBallMeasure n 1] base.u) := by
  let V : WeakFixedTraceCompetitor (base.dilate ε hε) :=
    WeakFixedTraceCompetitor.dilate base U ε hε
  obtain ⟨hMinLarge, hEqLarge⟩ := hLarge V
  have hBaseScale := base.unit_epsilon_energy_scaling hn ε hε
  have hUScale := U.field.unit_epsilon_energy_scaling hn ε hε
  have hFactor : 0 < ε ^ (n - 2) := pow_pos hε _
  constructor
  · calc
      weakBallEnergyEpsilon n 1 ε base.u base.grad =
          ε ^ (n - 2) * (base.dilate ε hε).energy := hBaseScale
      _ ≤ ε ^ (n - 2) * V.field.energy :=
        mul_le_mul_of_nonneg_left hMinLarge hFactor.le
      _ = weakBallEnergyEpsilon n 1 ε U.field.u U.field.grad :=
        hUScale.symm
  · intro hEq
    have hEqScaled : V.field.energy = (base.dilate ε hε).energy := by
      apply (mul_left_cancel₀ hFactor.ne')
      calc
        ε ^ (n - 2) * V.field.energy =
            weakBallEnergyEpsilon n 1 ε U.field.u U.field.grad :=
          hUScale.symm
        _ = weakBallEnergyEpsilon n 1 ε base.u base.grad := hEq
        _ = ε ^ (n - 2) * (base.dilate ε hε).energy := hBaseScale
    exact ae_eq_on_ball_of_dilate n 1 ε hε U.field.u base.u
      (hEqLarge hEqScaled)

end

end BrezisOP6
