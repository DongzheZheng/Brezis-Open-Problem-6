import BrezisOP6.EnergySharedQuotientDensityBound
import BrezisOP6.EnergyRegularNumeratorC1
import BrezisOP6.EnergyActualFieldsIntegrable

/-!
# Finite energy of the second profile times the shared quotient

The field `F(‖x‖) u(x)/f(‖x‖)` has the smooth representative
`[H_F(‖x‖²)/H_f(‖x‖²)]u(x)` on the ball. Its totalized value at the
origin is immaterial for the energy integral.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

theorem shared_quotient_second_product_GL_integrableOn_positiveBall
    (m : ℕ) (R : ℝ) (f F Hf HF : ℝ → ℝ)
    (β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hHf0 : Hf 0 = β) (hβ : 0 < β)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiff ℝ 1 u) :
    IntegrableOn
      (euclideanGLDensity (m + 3)
        (fun x : GLEuclidean (m + 3) =>
          F ‖x‖ • ((f ‖x‖)⁻¹ • u x)))
      (energyPositiveClosedBall (m + 3) R) volume := by
  let E := GLEuclidean (m + 3)
  let s : Set E := {x | Hf (‖x‖ ^ 2) ≠ 0}
  let v : E → E := fun x =>
    (HF (‖x‖ ^ 2) / Hf (‖x‖ ^ 2)) • u x
  have hsquare : ContDiff ℝ 1 (fun x : E => ‖x‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hsOpen : IsOpen s := by
    exact isOpen_ne_fun
      (hHf.continuous.comp hsquare.continuous)
      continuous_const
  have hclosed : Metric.closedBall (0 : E) R ⊆ s := by
    intro x hx
    exact radial_factor_ne_zero_on_closedBall (m + 3) R f Hf β
      hβ hHf0 hfFactor hfpos x hx
  have hnum : ContDiff ℝ 1 (fun x : E => HF (‖x‖ ^ 2)) :=
    hHF.comp hsquare
  have hden : ContDiff ℝ 1 (fun x : E => Hf (‖x‖ ^ 2)) :=
    hHf.comp hsquare
  have hv : ContDiffOn ℝ 1 v s :=
    (hnum.contDiffOn.div hden.contDiffOn (fun x hx => hx)).smul
      huC1.contDiffOn
  have hvClosed : IntegrableOn (euclideanGLDensity (m + 3) v)
      (Metric.closedBall (0 : E) R) volume :=
    euclideanGLDensity_integrableOn_closedBall_of_C1 (m + 3) R v
      (hv.continuousOn.mono hclosed)
      ((hv.continuousOn_fderiv_of_isOpen hsOpen (by norm_num)).mono hclosed)
  have hvBall : IntegrableOn (euclideanGLDensity (m + 3) v)
      (Metric.ball (0 : E) R) volume := by
    apply hvClosed.mono_set
    intro x hx
    have hr : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt hr
  have hEq : ∀ x ∈ Metric.ball (0 : E) R, x ≠ 0 →
      F ‖x‖ • ((f ‖x‖)⁻¹ • u x) = v x := by
    intro x hx hx0
    have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrle : ‖x‖ ≤ R := by
      have hrlt : ‖x‖ < R := by
        simpa only [Metric.mem_ball, dist_zero_right] using hx
      exact le_of_lt hrlt
    have hrne : ‖x‖ ≠ 0 := ne_of_gt hrpos
    have hHne : Hf (‖x‖ ^ 2) ≠ 0 :=
      hclosed (by simpa only [Metric.mem_closedBall, dist_zero_right]
        using hrle)
    change F ‖x‖ • ((f ‖x‖)⁻¹ • u x) =
      (HF (‖x‖ ^ 2) / Hf (‖x‖ ^ 2)) • u x
    rw [hfFactor ‖x‖ hrpos hrle, hFFactor ‖x‖ hrpos hrle,
      smul_smul]
    congr 1
    field_simp [hrne, hHne]
  have hBall := euclideanGLDensity_integrableOn_of_eq_off_origin_on_ball
    (m + 3) (by omega) R
    (fun x : E => F ‖x‖ • ((f ‖x‖)⁻¹ • u x))
    v hEq hvBall
  change Integrable _ (volume.restrict (energyPositiveClosedBall (m + 3) R))
  rw [energyPositiveClosedBall_restrict_eq_ball m R]
  exact hBall

end

end BrezisOP6
