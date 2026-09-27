import BrezisOP6.SphereUniformToL2
import BrezisOP6.EnergyRescaledTraceOrigin

/-!
# Uniform origin trace of the regular radial-factor quotient

For a continuous numerator and a continuous nonvanishing radial factor,
the removable expression `u(rω)/H(r²)` tends uniformly in the angular
variable to `u(0)/H(0)`.
-/

namespace BrezisOP6

open Filter Metric
open scoped Topology

noncomputable section

theorem radial_factor_quotient_uniform_origin
    (n : ℕ) (H : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hH : ContinuousAt H 0) (hH0 : H 0 ≠ 0)
    (hu : ContinuousAt u 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 ≤ r → r < δ →
        ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ‖(H (r ^ 2))⁻¹ • u (energySphereRay n ω r) -
            (H 0)⁻¹ • u 0‖ < ε := by
  intro ε hε
  let a : ℝ := (H 0)⁻¹
  let η : ℝ := min 1 (ε / (2 * (|a| + 1 + ‖u 0‖)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηBound : η * (|a| + 1 + ‖u 0‖) < ε := by
    have hle : η ≤ ε / (2 * (|a| + 1 + ‖u 0‖)) := min_le_right _ _
    have hpos : 0 < |a| + 1 + ‖u 0‖ := by positivity
    have hmul := mul_le_mul_of_nonneg_right hle hpos.le
    have hhalf : ε / (2 * (|a| + 1 + ‖u 0‖)) *
        (|a| + 1 + ‖u 0‖) = ε / 2 := by field_simp
    rw [hhalf] at hmul
    linarith
  have haCont : ContinuousAt (fun r : ℝ => (H (r ^ 2))⁻¹) 0 := by
    have hsq : ContinuousAt (fun r : ℝ => r ^ 2) 0 := by fun_prop
    have hcomp : ContinuousAt (fun r : ℝ => H (r ^ 2)) 0 := by
      simpa only [Function.comp_def] using
        hH.comp_of_eq hsq (by norm_num : (0 : ℝ) ^ 2 = 0)
    exact hcomp.inv₀ (by simpa using hH0)
  obtain ⟨δa, hδa, haδ⟩ :=
    (Metric.continuousAt_iff.mp haCont) η hη
  obtain ⟨δu, hδu, huδ⟩ :=
    continuousAt_origin_uniform_on_spheres n u hu η hη
  refine ⟨min δa δu, lt_min hδa hδu, ?_⟩
  intro r hr hrδ ω
  have hra : r < δa := lt_of_lt_of_le hrδ (min_le_left _ _)
  have hru : r < δu := lt_of_lt_of_le hrδ (min_le_right _ _)
  let ar : ℝ := (H (r ^ 2))⁻¹
  have har : |ar - a| < η := by
    have hdist : dist r 0 < δa := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hr] using hra
    have h := haδ hdist
    simpa [Real.dist_eq, ar, a] using h
  have hur : ‖u (energySphereRay n ω r) - u 0‖ < η :=
    huδ r hr hru ω
  have harBound : |ar| ≤ |a| + 1 := by
    have htri : |ar| ≤ |ar - a| + |a| := by
      convert abs_add_le (ar - a) a using 1 <;> ring
    linarith
  have hdecomp : ar • u (energySphereRay n ω r) - a • u 0 =
      ar • (u (energySphereRay n ω r) - u 0) + (ar - a) • u 0 := by
    module
  rw [show (H (r ^ 2))⁻¹ = ar from rfl,
    show (H 0)⁻¹ = a from rfl, hdecomp]
  calc
    ‖ar • (u (energySphereRay n ω r) - u 0) +
        (ar - a) • u 0‖ ≤
        ‖ar • (u (energySphereRay n ω r) - u 0)‖ +
          ‖(ar - a) • u 0‖ := norm_add_le _ _
    _ = |ar| * ‖u (energySphereRay n ω r) - u 0‖ +
        |ar - a| * ‖u 0‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (|a| + 1) * η + η * ‖u 0‖ := by
      have h1 := mul_le_mul_of_nonneg_left hur.le (abs_nonneg ar)
      have h2 := mul_le_mul_of_nonneg_right harBound hη.le
      have h3 := mul_le_mul_of_nonneg_right har.le (norm_nonneg (u 0))
      linarith
    _ < ε := by nlinarith [hηBound]

end

end BrezisOP6
