import BrezisOP6.EnergyC1Integrability

/-!
# The inverse-square energy singularity in dimensions at least three

The radial quotient of a smooth numerator by a positive-slope profile can
have an `r⁻¹` pole.  Its weighted gradient energy is dominated by an
inverse-square kernel.  The polar Haar criterion in the pinned mathlib
version proves that this kernel is integrable precisely on the side of the
dimension threshold needed for the present `m+3`-dimensional theorem.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

/-- A ball-local version of mathlib's global radial integrability criterion.
The truncation to `Ioo 0 R` is essential: `r⁻²` is generally not integrable
at infinity. -/
private theorem radial_integrableOn_ball_iff (m : ℕ) (R : ℝ)
    (f : ℝ → ℝ) :
    IntegrableOn (fun x : GLEuclidean (m + 3) => f ‖x‖)
      (Metric.ball (0 : GLEuclidean (m + 3)) R) volume ↔
    IntegrableOn (fun r : ℝ => r ^ (m + 2) * f r) (Ioo 0 R) volume := by
  letI : NeZero (m + 3) := ⟨by omega⟩
  let E := GLEuclidean (m + 3)
  let g : ℝ → ℝ := fun r => r ^ (m + 2) * f r
  calc
    _ ↔ Integrable (fun x : E => (Iio R).indicator f ‖x‖) volume := by
      rw [← integrable_indicator_iff measurableSet_ball]
      apply integrable_congr
      filter_upwards [] with x
      simp [indicator, Metric.mem_ball, dist_zero_right]
    _ ↔ IntegrableOn ((Ioo 0 R).indicator g) (Ioi 0) volume := by
      rw [integrable_fun_norm_addHaar (volume : Measure E)
        (f := (Iio R).indicator f), integrableOn_congr_fun _ measurableSet_Ioi]
      intro r hr
      have hdim : Module.finrank ℝ E - 1 = m + 2 := by
        simp [E, GLEuclidean]
      simp only [hdim, smul_eq_mul]
      have hrpos : 0 < r := hr
      by_cases hR : r < R <;> simp [g, indicator, hR, hrpos]
    _ ↔ Integrable ((Ioo 0 R).indicator g) volume := by
      rw [MeasureTheory.integrableOn_iff_integrable_of_support_subset]
      intro r hr
      simp only [support_indicator, mem_inter_iff] at hr
      exact hr.1.1
    _ ↔ IntegrableOn g (Ioo 0 R) volume := by
      rw [← integrable_indicator_iff measurableSet_Ioo]

/-- The kernel `‖x‖⁻²` is integrable on every finite ball in dimension
`m+3`.  The radial Jacobian cancels the pole to the ordinary polynomial
`r^m`. -/
theorem inverse_square_integrableOn_ball (m : ℕ) (R : ℝ) :
    IntegrableOn (fun x : GLEuclidean (m + 3) => ‖x‖⁻¹ ^ 2)
      (Metric.ball (0 : GLEuclidean (m + 3)) R) volume := by
  have hpoly : IntegrableOn (fun r : ℝ => r ^ m) (Ioo 0 R) volume :=
    (continuous_id.pow m).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hradial : IntegrableOn
      (fun r : ℝ => r ^ (m + 2) * r⁻¹ ^ 2) (Ioo 0 R) volume := by
    apply hpoly.congr_fun
    · intro r hr
      have hrne : r ≠ 0 := ne_of_gt hr.1
      symm
      calc
        r ^ (m + 2) * r⁻¹ ^ 2 = r ^ m * r ^ 2 * r⁻¹ ^ 2 := by
          rw [pow_add]
        _ = r ^ m := by field_simp [hrne]
    · exact measurableSet_Ioo
  exact (radial_integrableOn_ball_iff m R (fun r => r⁻¹ ^ 2)).2 hradial

/-- A measurable density with the sharp `O(1+r⁻²)` bound is integrable
on a finite ball.  Later quotient-gradient estimates provide the bound. -/
theorem integrableOn_ball_of_inverse_square_bound (m : ℕ)
    (R C : ℝ) (density : GLEuclidean (m + 3) → ℝ)
    (hmeas : AEStronglyMeasurable density
      ((volume : Measure (GLEuclidean (m + 3))).restrict
        (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hbound : ∀ᵐ x ∂(volume : Measure (GLEuclidean (m + 3))).restrict
      (Metric.ball (0 : GLEuclidean (m + 3)) R),
      ‖density x‖ ≤ C * (1 + ‖x‖⁻¹ ^ 2)) :
    IntegrableOn density
      (Metric.ball (0 : GLEuclidean (m + 3)) R) volume := by
  have hker := inverse_square_integrableOn_ball m R
  have hone : IntegrableOn (fun _ : GLEuclidean (m + 3) => (1 : ℝ))
      (Metric.ball (0 : GLEuclidean (m + 3)) R) volume := by
    exact integrableOn_const (measure_ball_ne_top)
  have hmaj : IntegrableOn
      (fun x : GLEuclidean (m + 3) => C * (1 + ‖x‖⁻¹ ^ 2))
      (Metric.ball (0 : GLEuclidean (m + 3)) R) volume :=
    (hone.add hker).const_mul C
  exact Integrable.mono' hmaj hmeas hbound

/-- Local inverse-square control at the collision point and ordinary
integrability on the remaining compact annulus give the full punctured-ball
integrability required by the energy identity. -/
theorem integrableOn_positiveBall_of_inner_outer (m : ℕ)
    (R δ : ℝ) (density : GLEuclidean (m + 3) → ℝ)
    (hinner : IntegrableOn density
      (Metric.ball (0 : GLEuclidean (m + 3)) δ) volume)
    (houter : IntegrableOn density
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R \
        Metric.ball (0 : GLEuclidean (m + 3)) δ) volume) :
    IntegrableOn density
      (energyPositiveClosedBall (m + 3) R) volume := by
  apply (hinner.union houter).mono_set
  intro x hx
  by_cases hδ : x ∈ Metric.ball (0 : GLEuclidean (m + 3)) δ
  · exact Or.inl hδ
  · exact Or.inr ⟨by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2,
      hδ⟩

/-- On the outer annulus, continuity supplies the integrability input of
the preceding gluing lemma. -/
theorem integrableOn_positiveBall_of_inner_continuous_outer (m : ℕ)
    (R δ : ℝ) (density : GLEuclidean (m + 3) → ℝ)
    (hinner : IntegrableOn density
      (Metric.ball (0 : GLEuclidean (m + 3)) δ) volume)
    (houterContinuous : ContinuousOn density
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R \
        Metric.ball (0 : GLEuclidean (m + 3)) δ)) :
    IntegrableOn density
      (energyPositiveClosedBall (m + 3) R) volume := by
  have hcompact : IsCompact
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R \
        Metric.ball (0 : GLEuclidean (m + 3)) δ) :=
    (isCompact_closedBall _ _).diff isOpen_ball
  exact integrableOn_positiveBall_of_inner_outer m R δ density hinner
    (houterContinuous.integrableOn_compact hcompact)

end

end BrezisOP6
