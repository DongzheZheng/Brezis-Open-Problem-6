import BrezisOP6.EnergyQuotientGradientBound
import BrezisOP6.EnergyC1Integrability
import BrezisOP6.EnergyActualInteriorPair

/-!
# Uniform weighted bounds for the actual smooth quotient

The regular origin factor f(r)=r H(r²) and positivity of f on (0,R]
make r/f(r) bounded on the full radius interval.  Combined with compact
C¹ bounds on the competitor and profile, the weighted quotient gradient
has one global inverse-square majorant.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

theorem actual_quotient_global_weighted_bounds
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f H : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hH : ContDiff ℝ 1 H)
    (huC1 : ContDiff ℝ 1 u)
    (hH0 : H 0 ≠ 0)
    (hf : ∀ r, 0 < r → r ≤ R → f r = r * H (r ^ 2))
    (hfpos : ∀ r, 0 < r → r ≤ R → 0 < f r) :
    ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ x : GLEuclidean (m + 3),
        0 < ‖x‖ → ‖x‖ < R →
          f ‖x‖ ^ 2 * euclideanGradientSq (m + 3)
            (fun y => (f ‖y‖)⁻¹ • u y) x ≤
              A + B * ‖x‖⁻¹ ^ 2 ∧
          f ‖x‖ ^ 2 * ‖(f ‖x‖)⁻¹ • u x‖ ^ 2 ≤ C := by
  have hHne : ∀ r ∈ Icc (0 : ℝ) R, H (r ^ 2) ≠ 0 := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hzero | hrpos
    · subst r
      simpa using hH0
    · intro hzero
      have hfr := hf r hrpos hr.2
      rw [hzero, mul_zero] at hfr
      exact (ne_of_gt (hfpos r hrpos hr.2)) hfr
  have hHinv : ContinuousOn
      (fun r : ℝ => (H (r ^ 2))⁻¹) (Icc 0 R) :=
    ((hH.continuous.comp (continuous_id.pow 2)).continuousOn).inv₀
      hHne
  obtain ⟨Cr, hCr⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hHinv
  obtain ⟨Cd, hCd⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn
      hdfC1.continuous.continuousOn
  obtain ⟨Cu, Cg, hCu0, hCg0, hUbounds⟩ :=
    euclideanC1_closedBall_bounds (m + 3) R u
      huC1.continuous.continuousOn
      (huC1.continuous_fderiv (by norm_num)).continuousOn
  let Cr' : ℝ := max Cr 0
  let Cd' : ℝ := max Cd 0
  have hCr0 : 0 ≤ Cr' := le_max_right _ _
  have hCd0 : 0 ≤ Cd' := le_max_right _ _
  refine ⟨2 * Cg, 2 * Cd' ^ 2 * Cr' ^ 2 * Cu ^ 2,
    Cu ^ 2, by positivity, by positivity, by positivity, ?_⟩
  intro x hx hrR
  have hr : ‖x‖ ∈ Icc (0 : ℝ) R :=
    ⟨hx.le, hrR.le⟩
  have hxBall : x ∈ Metric.closedBall
      (0 : GLEuclidean (m + 3)) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hrR.le
  obtain ⟨huBound, hgradBound⟩ := hUbounds x hxBall
  have hfr : 0 < f ‖x‖ := hfpos ‖x‖ hx hrR.le
  have hHxr : H (‖x‖ ^ 2) ≠ 0 := hHne ‖x‖ hr
  have hratioEq : ‖x‖ / f ‖x‖ = (H (‖x‖ ^ 2))⁻¹ := by
    rw [hf ‖x‖ hx hrR.le]
    field_simp [ne_of_gt hx, hHxr]
  have hratio : |‖x‖ / f ‖x‖| ≤ Cr' := by
    rw [hratioEq]
    have h := hCr ‖x‖ hr
    simpa only [Real.norm_eq_abs] using h.trans (le_max_left _ _)
  have hdp : |deriv f ‖x‖| ≤ Cd' := by
    have h := hCd ‖x‖ hr
    simpa only [Real.norm_eq_abs] using h.trans (le_max_left _ _)
  have hxne : x ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt hx)
  have hp : HasDerivAt f (deriv f ‖x‖) ‖x‖ :=
    (hfC1.differentiable_one ‖x‖).hasDerivAt
  have hgrad := energyQuotient_weighted_gradient_le_inverse_square
    (m + 3) f u x (deriv f ‖x‖) Cd' Cr' Cu Cg
    hxne hp (ne_of_gt hfr)
    (huC1.differentiable_one x) hCd0 hCr0 hCu0
    hdp hratio huBound hgradBound
  constructor
  · exact hgrad
  · have hnorm :
        f ‖x‖ ^ 2 * ‖(f ‖x‖)⁻¹ • u x‖ ^ 2 =
          ‖u x‖ ^ 2 := by
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp [ne_of_gt hfr]
    rw [hnorm]
    exact (sq_le_sq₀ (norm_nonneg _) hCu0).2 huBound

end

end BrezisOP6
