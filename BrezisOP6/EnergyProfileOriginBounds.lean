import BrezisOP6.OriginFluxFactor

/-!
# Uniform numerical bounds from a regular radial origin

The differentiated Taylor ansatz with positive initial slope supplies the
local profile bounds needed by `quotient_inner_flux_envelope_of_continuity`.
The derivative, profile, and reciprocal-slope bounds are derived from
one-sided limits; none is included as a hypothesis.
-/

namespace BrezisOP6

open Filter Topology

noncomputable section

/-- The first-derivative component of the regular-origin Taylor data
converges to its leading slope. -/
theorem radial_origin_deriv_limit
    {p : ℝ → ℝ} {α A B : ℝ}
    (h : RadialOriginTaylor p α A B) :
    Tendsto (deriv p) (𝓝[>] (0 : ℝ)) (𝓝 α) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hA : Tendsto (fun r : ℝ => 3 * A * r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds (x := 3 * A)).mul (hr.pow 2) using 1
    simp
  have hB : Tendsto (fun r : ℝ => 5 * B * r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds (x := 5 * B)).mul (hr.pow 4) using 1
    simp
  have he : Tendsto (fun r : ℝ => r ^ 4 * h.e₁ r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (hr.pow 4).mul h.e₁_zero using 1
    simp
  have hformula : Tendsto
      (fun r : ℝ => α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * h.e₁ r)
      (𝓝[>] (0 : ℝ)) (𝓝 α) := by
    convert ((tendsto_const_nhds (x := α)).add hA).add
      (hB.add he) using 1
    · funext r; ring
    · simp
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      deriv p r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * h.e₁ r := by
    filter_upwards [self_mem_nhdsWithin] with r hrpos
    exact h.first r hrpos
  exact (tendsto_congr' heq).2 hformula

/-- All four quantitative inputs of the uniform quotient-flux envelope
follow near the origin from the Taylor data and a positive slope. -/
theorem radial_origin_local_flux_bounds
    {p : ℝ → ℝ} {α A B : ℝ}
    (hα : 0 < α) (h : RadialOriginTaylor p α A B) :
    ∃ δ Cdp Cratio Cp : ℝ,
      0 < δ ∧ 0 ≤ Cdp ∧ 0 ≤ Cratio ∧ 0 ≤ Cp ∧
      ∀ r : ℝ, 0 < r → r < δ →
        p r ≠ 0 ∧ |deriv p r| ≤ Cdp ∧
          |r / p r| ≤ Cratio ∧ |p r| ≤ Cp := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hdiv : Tendsto (fun r : ℝ => p r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    profile_div_radius_origin_limit h
  have hdivpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < p r / r :=
    hdiv.eventually (eventually_gt_nhds hα)
  have hinv : Tendsto (fun r : ℝ => (p r / r)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 α⁻¹) := by
    simpa using hdiv.inv₀ (ne_of_gt hα)
  have heqratio : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      r / p r = (p r / r)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin, hdivpos] with r hrpos hpdiv
    have hppos : 0 < p r :=
      (div_pos_iff_of_pos_right (show 0 < r from hrpos)).mp hpdiv
    field_simp [ne_of_gt (show 0 < r from hrpos), ne_of_gt hppos]
  have hratio : Tendsto (fun r : ℝ => r / p r)
      (𝓝[>] (0 : ℝ)) (𝓝 α⁻¹) :=
    (tendsto_congr' heqratio).2 hinv
  have heqp : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      p r = (p r / r) * r := by
    filter_upwards [self_mem_nhdsWithin] with r hrpos
    field_simp [ne_of_gt (show 0 < r from hrpos)]
  have hpzero : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hprod := (tendsto_congr' heqp).2 (hdiv.mul hr)
    simpa using hprod
  have hdp : Tendsto (deriv p) (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    radial_origin_deriv_limit h
  have hdpBound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |deriv p r| < |α| + 1 :=
    hdp.abs.eventually (eventually_lt_nhds (by linarith))
  have hratioBound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |r / p r| < |α⁻¹| + 1 :=
    hratio.abs.eventually (eventually_lt_nhds (by linarith))
  have hpBound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |p r| < 1 := by
    simpa using hpzero.abs.eventually
      (eventually_lt_nhds (by norm_num))
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      p r ≠ 0 ∧ |deriv p r| ≤ |α| + 1 ∧
        |r / p r| ≤ |α⁻¹| + 1 ∧ |p r| ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, hdivpos,
      hdpBound, hratioBound, hpBound]
      with r hrpos hpdiv hdp' hratio' hp'
    have hppos : 0 < p r :=
      (div_pos_iff_of_pos_right (show 0 < r from hrpos)).mp hpdiv
    exact ⟨ne_of_gt hppos, le_of_lt hdp',
      le_of_lt hratio', le_of_lt hp'⟩
  obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hevent
  refine ⟨δ, |α| + 1, |α⁻¹| + 1, 1, hδpos,
    by positivity, by positivity, by norm_num, ?_⟩
  intro r hrpos hrδ
  exact hδ ⟨hrpos, hrδ⟩

/-- Finite-ball Taylor data suffice, with the neighborhood explicitly
contained in the ball radius.  No ODE or profile bounds beyond `R` enter. -/
theorem radial_origin_local_flux_bounds_on
    {p : ℝ → ℝ} {α A B R : ℝ}
    (hR : 0 < R) (hα : 0 < α)
    (h : RadialOriginTaylorOn p α A B R) :
    ∃ δ Cdp Cratio Cp : ℝ,
      0 < δ ∧ δ ≤ R ∧ 0 ≤ Cdp ∧ 0 ≤ Cratio ∧ 0 ≤ Cp ∧
      ∀ r : ℝ, 0 < r → r < δ →
        p r ≠ 0 ∧ |deriv p r| ≤ Cdp ∧
          |r / p r| ≤ Cratio ∧ |p r| ≤ Cp := by
  obtain ⟨δ, Cdp, Cratio, Cp, hδpos, hCdp, hCratio, hCp, hbound⟩ :=
    radial_origin_local_flux_bounds hα (h.toGlobal hR)
  refine ⟨min δ R, Cdp, Cratio, Cp, lt_min hδpos hR,
    min_le_right δ R, hCdp, hCratio, hCp, ?_⟩
  intro r hrpos hrδ
  exact hbound r hrpos (lt_of_lt_of_le hrδ (min_le_left δ R))

end

end BrezisOP6
