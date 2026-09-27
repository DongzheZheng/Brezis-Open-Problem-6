import BrezisOP6.EnergyVortexPointwise

/-!
# From equality on spherical rays to equality on the punctured ball

This is the final geometric identification in the equality argument.  It
contains no measure-theoretic or elliptic regularity input.
-/

namespace BrezisOP6

open Metric Set

noncomputable section

theorem vortex_eq_of_quotient_eq_on_rays
    (n : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hfpos : ∀ r : ℝ, 0 < r → r < R → 0 < f r)
    (hRays : ∀ r : ℝ, r ∈ Ioo (0 : ℝ) R →
      ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (f ‖r • (ω : GLEuclidean n)‖)⁻¹ •
          u (r • (ω : GLEuclidean n)) =
            (ω : GLEuclidean n)) :
    ∀ x : GLEuclidean n, x ∈ Metric.ball (0 : GLEuclidean n) R →
      x ≠ 0 → u x = radialVortex n f x := by
  intro x hxBall hx0
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hrR : ‖x‖ < R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxBall
  have hωnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    exact inv_mul_cancel₀ (ne_of_gt hr)
  let ω : Metric.sphere (0 : GLEuclidean n) 1 :=
    ⟨‖x‖⁻¹ • x, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hωnorm⟩
  have hrω : ‖x‖ • (ω : GLEuclidean n) = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  have hRay := hRays ‖x‖ ⟨hr, hrR⟩ ω
  rw [hrω] at hRay
  have hfne : f ‖x‖ ≠ 0 := ne_of_gt (hfpos ‖x‖ hr hrR)
  have hu : u x = f ‖x‖ • (ω : GLEuclidean n) := by
    calc
      u x = f ‖x‖ • ((f ‖x‖)⁻¹ • u x) := by
        rw [smul_smul, mul_inv_cancel₀ hfne, one_smul]
      _ = f ‖x‖ • (ω : GLEuclidean n) := by rw [hRay]
  calc
    u x = f ‖x‖ • (ω : GLEuclidean n) := hu
    _ = radialVortex n f x := by
      change f ‖x‖ • (‖x‖⁻¹ • x) = (f ‖x‖ / ‖x‖) • x
      simp only [smul_smul, div_eq_mul_inv]

end

end BrezisOP6
