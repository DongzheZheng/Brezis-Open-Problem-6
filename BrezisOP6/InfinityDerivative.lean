import BrezisOP6.InfinityFirstOrder

/-!
# Derivative control for the far-field radial profile

The zero-mode terminal sign needs one derivative more than the positional
Laurent expansion.  This file isolates the precise derivative remainder and
then derives the sign from it.  A separate short-interval ODE interpolation
argument is used to obtain that remainder from the sixth-order enclosure.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- A local interpolation estimate on a unit interval.  The value bound
finds one small derivative by the mean value theorem; the curvature bound
transfers it to every point of the interval. -/
private theorem unit_derivative_bound_of_curvature_bound
    (w : ℝ → ℝ) (t A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hwdiff : ∀ x ∈ Set.Icc t (t + 1),
      DifferentiableAt ℝ w x)
    (hw2diff : ∀ x ∈ Set.Icc t (t + 1),
      DifferentiableAt ℝ (deriv w) x)
    (hwb : ∀ x ∈ Set.Icc t (t + 1), |w x| ≤ A)
    (hsecond : ∀ x ∈ Set.Icc t (t + 1),
      |deriv (deriv w) x| ≤ B) :
    ∀ x ∈ Set.Icc t (t + 1), |deriv w x| ≤ 2 * A + B := by
  have hinterval : t < t + 1 := by linarith
  have hwcont : ContinuousOn w (Set.Icc t (t + 1)) := by
    intro x hx
    exact (hwdiff x hx).continuousAt.continuousWithinAt
  have hwdiffOn : DifferentiableOn ℝ w (Set.Ioo t (t + 1)) := by
    intro x hx
    exact (hwdiff x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).differentiableWithinAt
  obtain ⟨s, hs, hsd⟩ :=
    exists_deriv_eq_slope w hinterval hwcont hwdiffOn
  have hsder : deriv w s = w (t + 1) - w t := by
    convert hsd using 1 <;> ring
  have hsmall : |deriv w s| ≤ 2 * A := by
    rw [hsder]
    have h₀ := hwb t ⟨le_rfl, le_of_lt hinterval⟩
    have h₁ := hwb (t + 1) ⟨le_of_lt hinterval, le_rfl⟩
    have htri := abs_sub (w (t + 1)) (w t)
    linarith
  have hdiff_bound : ∀ a b : ℝ,
      t ≤ a → b ≤ t + 1 → a < b →
      |deriv w b - deriv w a| ≤ B * (b - a) := by
    intro a b ha hb hab
    have habI : ∀ x ∈ Set.Icc a b, x ∈ Set.Icc t (t + 1) := by
      intro x hx
      exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
    have hdc : ContinuousOn (deriv w) (Set.Icc a b) := by
      intro x hx
      exact (hw2diff x (habI x hx)).continuousAt.continuousWithinAt
    have hdd : DifferentiableOn ℝ (deriv w) (Set.Ioo a b) := by
      intro x hx
      exact (hw2diff x (habI x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).differentiableWithinAt
    obtain ⟨ξ, hξ, hξder⟩ :=
      exists_deriv_eq_slope (deriv w) hab hdc hdd
    have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    have heq : deriv w b - deriv w a =
        deriv (deriv w) ξ * (b - a) := by
      have hmul := (eq_div_iff hden).mp hξder
      nlinarith [hmul]
    rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hab)]
    exact mul_le_mul_of_nonneg_right
      (hsecond ξ (habI ξ ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩))
      (sub_nonneg.mpr hab.le)
  intro x hx
  rcases lt_trichotomy x s with hxs | hxs | hsx
  · have hdiff := hdiff_bound x s hx.1 (le_of_lt hs.2) hxs
    have hwidth : s - x ≤ 1 := by linarith [hx.1, hs.2]
    have hsmallWidth : B * (s - x) ≤ B := by
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hwidth)]
    have htri : |deriv w x| ≤
        |deriv w x - deriv w s| + |deriv w s| := by
      convert abs_add_le (deriv w x - deriv w s) (deriv w s) using 1 <;> ring
    rw [abs_sub_comm] at htri
    linarith
  · subst x
    linarith
  · have hdiff := hdiff_bound s x (le_of_lt hs.1) hx.2 hsx
    have hwidth : x - s ≤ 1 := by linarith [hx.2, hs.1]
    have hsmallWidth : B * (x - s) ≤ B := by
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hwidth)]
    have htri : |deriv w x| ≤
        |deriv w x - deriv w s| + |deriv w s| := by
      convert abs_add_le (deriv w x - deriv w s) (deriv w s) using 1 <;> ring
    linarith

/-- The curvature may contain a small multiple of the unknown derivative.
Compactness supplies its maximum, which can then be absorbed. -/
private theorem unit_derivative_bound_of_linear_curvature
    (w : ℝ → ℝ) (t A B lam : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (hlamsmall : lam ≤ 1 / 2)
    (hwdiff : ∀ x ∈ Set.Icc t (t + 1),
      DifferentiableAt ℝ w x)
    (hw2diff : ∀ x ∈ Set.Icc t (t + 1),
      DifferentiableAt ℝ (deriv w) x)
    (hwb : ∀ x ∈ Set.Icc t (t + 1), |w x| ≤ A)
    (hcurv : ∀ x ∈ Set.Icc t (t + 1),
      |deriv (deriv w) x| ≤ lam * |deriv w x| + B) :
    ∀ x ∈ Set.Icc t (t + 1), |deriv w x| ≤ 4 * A + 2 * B := by
  have hinterval : t < t + 1 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => |deriv w x|)
      (Set.Icc t (t + 1)) := by
    intro x hx
    exact ((hw2diff x hx).continuousAt.abs).continuousWithinAt
  obtain ⟨c, hc, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (show (Set.Icc t (t + 1)).Nonempty from
        ⟨t, ⟨le_rfl, le_of_lt hinterval⟩⟩) hcont
  let B' : ℝ := lam * |deriv w c| + B
  have hB' : 0 ≤ B' := by
    dsimp [B']
    exact add_nonneg (mul_nonneg hlam (abs_nonneg _)) hB
  have hcurv' : ∀ x ∈ Set.Icc t (t + 1),
      |deriv (deriv w) x| ≤ B' := by
    intro x hx
    have hxc : |deriv w x| ≤ |deriv w c| := hmax hx
    dsimp [B']
    have hmul := mul_le_mul_of_nonneg_left hxc hlam
    linarith [hcurv x hx]
  have hM := unit_derivative_bound_of_curvature_bound
    w t A B' hA hB' hwdiff hw2diff hwb hcurv' c hc
  have hlamM : lam * |deriv w c| ≤ |deriv w c| / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlamsmall)
      (abs_nonneg (deriv w c))]
  have hM' : |deriv w c| ≤ 4 * A + 2 * B := by
    dsimp [B'] at hM
    linarith
  intro x hx
  exact (hmax hx).trans hM'

/-- Local ODE interpolation: sixth-order bounds for the profile and the
non-derivative forcing imply the same bound for its derivative at the right
endpoint.  The coefficient `γ/x` is absorbed once `t ≥ 2γ`. -/
theorem unit_derivative_bound_from_radial_ode
    (w g : ℝ → ℝ) (γ C D t : ℝ)
    (hγ : 0 ≤ γ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ht : 0 < t) (hlarge : 2 * γ ≤ t)
    (hwdiff : ∀ x ∈ Set.Icc t (t + 1),
      DifferentiableAt ℝ w x)
    (hw2diff : ∀ x ∈ Set.Icc t (t + 1),
      DifferentiableAt ℝ (deriv w) x)
    (hwb : ∀ x ∈ Set.Icc t (t + 1),
      |w x| ≤ C * t ^ (-6 : ℤ))
    (hgb : ∀ x ∈ Set.Icc t (t + 1),
      |g x| ≤ D * t ^ (-6 : ℤ))
    (hode : ∀ x ∈ Set.Icc t (t + 1),
      deriv (deriv w) x + γ / x * deriv w x = g x) :
    |deriv w (t + 1)| ≤
      (4 * C + 2 * D) * t ^ (-6 : ℤ) := by
  have htinv : 0 ≤ t ^ (-6 : ℤ) := by positivity
  have hA : 0 ≤ C * t ^ (-6 : ℤ) := mul_nonneg hC htinv
  have hB : 0 ≤ D * t ^ (-6 : ℤ) := mul_nonneg hD htinv
  have hlam : 0 ≤ γ / t := div_nonneg hγ (le_of_lt ht)
  have hlamsmall : γ / t ≤ 1 / 2 := by
    apply (div_le_iff₀ ht).mpr
    nlinarith
  have hcurv : ∀ x ∈ Set.Icc t (t + 1),
      |deriv (deriv w) x| ≤
        (γ / t) * |deriv w x| + D * t ^ (-6 : ℤ) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ht hx.1
    have hrat : γ / x ≤ γ / t := by
      apply (div_le_div_iff₀ hxpos ht).mpr
      nlinarith [mul_nonneg hγ (sub_nonneg.mpr hx.1)]
    have hγx : 0 ≤ γ / x := div_nonneg hγ (le_of_lt hxpos)
    have hmul : |γ / x * deriv w x| ≤
        (γ / t) * |deriv w x| := by
      rw [abs_mul, abs_of_nonneg hγx]
      exact mul_le_mul_of_nonneg_right hrat (abs_nonneg _)
    have hodeEq : deriv (deriv w) x =
        g x - γ / x * deriv w x := by
      linarith [hode x hx]
    rw [hodeEq]
    have htri := abs_sub (g x) (γ / x * deriv w x)
    linarith [hgb x hx]
  have hbound := unit_derivative_bound_of_linear_curvature
    w t (C * t ^ (-6 : ℤ)) (D * t ^ (-6 : ℤ))
    (γ / t) hA hB hlam hlamsmall hwdiff hw2diff hwb hcurv
    (t + 1) ⟨by linarith, le_rfl⟩
  convert hbound using 1 <;> ring

private theorem inverseSixth_antitone
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-6 : ℤ) ≤ a ^ (-6 : ℤ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpow : a ^ 6 ≤ b ^ 6 := by gcongr
  have hdiv : 1 / b ^ 6 ≤ 1 / a ^ 6 := by
    apply (div_le_div_iff₀ (pow_pos hb 6) (pow_pos ha 6)).mpr
    nlinarith
  simpa only [zpow_neg, one_div] using hdiv

private theorem inverseSixth_shift_bound
    {r : ℝ} (hr : 2 ≤ r) :
    (r - 1) ^ (-6 : ℤ) ≤ 64 * r ^ (-6 : ℤ) := by
  have hrpos : 0 < r := by linarith
  have htpos : 0 < r - 1 := by linarith
  have hlinear : r ≤ 2 * (r - 1) := by linarith
  have hpow : r ^ 6 ≤ (2 * (r - 1)) ^ 6 := by gcongr
  have hdiv : 1 / (r - 1) ^ 6 ≤ 64 / r ^ 6 := by
    apply (div_le_div_iff₀ (pow_pos htpos 6) (pow_pos hrpos 6)).mpr
    nlinarith [hpow]
  simpa only [zpow_neg, one_div] using hdiv

private theorem sixth_bound_of_scaled_zero
    {w : ℝ → ℝ}
    (hlim : Filter.Tendsto (fun r : ℝ => r ^ 6 * w r)
      Filter.atTop (𝓝 (0 : ℝ))) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r → 0 < r →
      |w r| ≤ r ^ (-6 : ℤ) := by
  have hsmall : ∀ᶠ r : ℝ in Filter.atTop,
      |r ^ 6 * w r| < 1 :=
    hlim.abs.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨R, ?_⟩
  intro r hrR hr
  have hpow : 0 < r ^ 6 := pow_pos hr 6
  have hmul : r ^ 6 * |w r| < 1 := by
    simpa only [abs_mul, abs_of_pos hpow] using hR r hrR
  have hdiv : |w r| ≤ 1 / r ^ 6 := by
    apply (le_div_iff₀ hpow).mpr
    nlinarith
  simpa only [zpow_neg, one_div] using hdiv

/-- The short-interval interpolation argument yields a global sixth-order
derivative estimate from scaled sixth-order position and forcing limits.
No derivative asymptotic is assumed. -/
theorem derivative_sixth_bound_of_scaled_ode
    {w g : ℝ → ℝ} {γ : ℝ}
    (hγ : 0 ≤ γ)
    (hwdiff : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ w r)
    (hw2diff : ∀ r : ℝ, 0 < r →
      DifferentiableAt ℝ (deriv w) r)
    (hode : ∀ r : ℝ, 0 < r →
      deriv (deriv w) r + γ / r * deriv w r = g r)
    (hwlim : Filter.Tendsto (fun r : ℝ => r ^ 6 * w r)
      Filter.atTop (𝓝 (0 : ℝ)))
    (hglim : Filter.Tendsto (fun r : ℝ => r ^ 6 * g r)
      Filter.atTop (𝓝 (0 : ℝ))) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r → 0 < r →
      |deriv w r| ≤ 384 * r ^ (-6 : ℤ) := by
  obtain ⟨Rw, hwbound⟩ := sixth_bound_of_scaled_zero hwlim
  obtain ⟨Rg, hgbound⟩ := sixth_bound_of_scaled_zero hglim
  let T : ℝ := max (max Rw Rg) (max 1 (2 * γ))
  refine ⟨T + 1, ?_⟩
  intro r hrT _hr
  let t : ℝ := r - 1
  have htRw : Rw ≤ t := by dsimp [t, T] at *; linarith [le_max_left Rw Rg, le_max_left (max Rw Rg) (max 1 (2 * γ))]
  have htRg : Rg ≤ t := by dsimp [t, T] at *; linarith [le_max_right Rw Rg, le_max_left (max Rw Rg) (max 1 (2 * γ))]
  have ht1 : 1 ≤ t := by dsimp [t, T] at *; linarith [le_max_left (1 : ℝ) (2 * γ), le_max_right (max Rw Rg) (max 1 (2 * γ))]
  have htlarge : 2 * γ ≤ t := by dsimp [t, T] at *; linarith [le_max_right (1 : ℝ) (2 * γ), le_max_right (max Rw Rg) (max 1 (2 * γ))]
  have htpos : 0 < t := by linarith
  have hunitW : ∀ x ∈ Set.Icc t (t + 1),
      |w x| ≤ t ^ (-6 : ℤ) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le htpos hx.1
    exact (hwbound x (le_trans htRw hx.1) hxpos).trans
      (inverseSixth_antitone htpos hx.1)
  have hunitG : ∀ x ∈ Set.Icc t (t + 1),
      |g x| ≤ t ^ (-6 : ℤ) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le htpos hx.1
    exact (hgbound x (le_trans htRg hx.1) hxpos).trans
      (inverseSixth_antitone htpos hx.1)
  have hunit := unit_derivative_bound_from_radial_ode
    w g γ 1 1 t hγ (by norm_num) (by norm_num) htpos htlarge
    (fun x hx => hwdiff x (lt_of_lt_of_le htpos hx.1))
    (fun x hx => hw2diff x (lt_of_lt_of_le htpos hx.1))
    (by simpa using hunitW) (by simpa using hunitG)
    (fun x hx => hode x (lt_of_lt_of_le htpos hx.1))
  have hr2 : 2 ≤ r := by dsimp [t] at ht1; linarith
  have hshift := inverseSixth_shift_bound hr2
  have hunit' : |deriv w r| ≤ 6 * t ^ (-6 : ℤ) := by
    convert hunit using 1 <;> dsimp [t] <;> ring
  calc
    |deriv w r| ≤ 6 * t ^ (-6 : ℤ) := hunit'
    _ ≤ 6 * (64 * r ^ (-6 : ℤ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [t] using hshift) (by norm_num)
    _ = 384 * r ^ (-6 : ℤ) := by ring

/-- Rewriting the already established sixth-order Laurent coefficient as
decay of the exact profile-minus-candidate difference. -/
theorem sixth_difference_scaled_zero_of_coefficient
    {F : ℝ → ℝ} {a b c : ℝ}
    (hcoeff : Filter.Tendsto
      (fun r : ℝ => r ^ 6 *
        (F r - 1 + a * r ^ (-2 : ℤ) -
          b * r ^ (-4 : ℤ)))
      Filter.atTop (𝓝 c)) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 6 * (F r - farCandidate a b c r))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have hsub : Filter.Tendsto
      (fun r : ℝ => r ^ 6 *
        (F r - 1 + a * r ^ (-2 : ℤ) -
          b * r ^ (-4 : ℤ)) - c)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert hcoeff.sub (tendsto_const_nhds (x := c)) using 1 <;> ring
  apply hsub.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
  unfold farCandidate
  simp only [zpow_neg]
  field_simp [ne_of_gt hr]
  ring

/-- The linearized zeroth-order coefficient at the vacuum profile tends to
`-2`; its boundedness costs no additional profile hypothesis. -/
theorem far_linearized_coefficient_tendsto
    {F : ℝ → ℝ} (n a b c : ℝ)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ))) :
    Filter.Tendsto
      (fun r : ℝ => 1 - (n - 1) / r ^ 2 -
        (F r ^ 2 + F r * farCandidate a b c r +
          farCandidate a b c r ^ 2))
      Filter.atTop (𝓝 (-2 : ℝ)) := by
  have hq : Filter.Tendsto (farCandidate a b c)
      Filter.atTop (𝓝 (1 : ℝ)) :=
    sixthCandidate_tendsto_one a b c
  have hrad : Filter.Tendsto
      (fun r : ℝ => (n - 1) / r ^ 2)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := n - 1)).mul
      invSquare_tendsto_zero using 1 <;>
      simp only [zpow_neg, div_eq_mul_inv, mul_zero]
  have hcubic : Filter.Tendsto
      (fun r : ℝ => F r ^ 2 + F r * farCandidate a b c r +
        farCandidate a b c r ^ 2)
      Filter.atTop (𝓝 (3 : ℝ)) := by
    convert ((hFone.pow 2).add (hFone.mul hq)).add (hq.pow 2)
      using 1 <;> norm_num
  convert ((tendsto_const_nhds (x := (1 : ℝ))).sub hrad).sub hcubic
    using 1 <;> norm_num

/-- The exact sixth-order Laurent candidate has residual `o(r⁻⁶)` once
its coefficient is chosen to cancel the leading residual. -/
theorem sixth_candidate_scaled_residual_zero (n : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 6 * farResidual n r
        (farCandidate ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8)
          (farCoeff6Residual n / 2) r)
        (farCandidateD1 ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8)
          (farCoeff6Residual n / 2) r)
        (farCandidateD2 ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8)
          (farCoeff6Residual n / 2) r))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  convert far_q1_scaled_residual_limit n (farCoeff6Residual n / 2)
    using 1 <;> ring

/-- The ODE and the already proved positional expansion control the
derivative remainder.  This is the unit-interval argument of the manuscript
formalized without assuming an asymptotic expansion for `F'`. -/
theorem radial_profile_derivative_sixth_bound
    {F : ℝ → ℝ} {n : ℝ}
    (hn : 1 ≤ n)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r → 0 < r →
      |deriv F r - farCandidateD1 ((n - 1) / 2)
        (3 * (n - 1) * (n - 5) / 8)
        (farCoeff6Residual n / 2) r| ≤
        384 * r ^ (-6 : ℤ) := by
  let a : ℝ := (n - 1) / 2
  let b : ℝ := 3 * (n - 1) * (n - 5) / 8
  let c : ℝ := farCoeff6Residual n / 2
  let q : ℝ → ℝ := farCandidate a b c
  let q₁ : ℝ → ℝ := farCandidateD1 a b c
  let q₂ : ℝ → ℝ := farCandidateD2 a b c
  let w : ℝ → ℝ := fun r => F r - q r
  let κ : ℝ → ℝ := fun r =>
    1 - (n - 1) / r ^ 2 - (F r ^ 2 + F r * q r + q r ^ 2)
  let e : ℝ → ℝ := fun r =>
    farResidual n r (q r) (q₁ r) (q₂ r)
  let g : ℝ → ℝ := fun r => -κ r * w r - e r
  have hcoeff := radial_profile_third_coefficient hn
    hFone hFdiff hF2diff hFode
  have hwlim : Filter.Tendsto (fun r : ℝ => r ^ 6 * w r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    exact sixth_difference_scaled_zero_of_coefficient
      (a := a) (b := b) (c := c)
      (by simpa [a, b, c] using hcoeff)
  have hκlim : Filter.Tendsto κ Filter.atTop (𝓝 (-2 : ℝ)) := by
    simpa [κ, q] using
      far_linearized_coefficient_tendsto n a b c hFone
  have helim : Filter.Tendsto (fun r : ℝ => r ^ 6 * e r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [e, q, q₁, q₂, a, b, c] using
      sixth_candidate_scaled_residual_zero n
  have hglim : Filter.Tendsto (fun r : ℝ => r ^ 6 * g r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    have hmul : Filter.Tendsto
        (fun r : ℝ => κ r * (r ^ 6 * w r))
        Filter.atTop (𝓝 (0 : ℝ)) := by
      convert hκlim.mul hwlim using 1 <;> ring
    have hsum := hmul.neg.sub helim
    have hsum' : Filter.Tendsto
        (fun r : ℝ => -(κ r * (r ^ 6 * w r)) - r ^ 6 * e r)
        Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero, sub_zero] using hsum
    apply hsum'.congr'
    filter_upwards [] with r
    dsimp [g]
    ring
  have hwder : ∀ r : ℝ, 0 < r →
      HasDerivAt w (deriv F r - q₁ r) r := by
    intro r hr
    simpa [w, q, q₁] using
      ((hFdiff r).hasDerivAt.sub
        (farCandidate_hasDerivAt a b c r (ne_of_gt hr)))
  have hwder₂ : ∀ r : ℝ, 0 < r →
      HasDerivAt (deriv w)
        (deriv (deriv F) r - q₂ r) r := by
    intro r hr
    have hEq : deriv w =ᶠ[𝓝 r]
        (fun x => deriv F x - q₁ x) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
      exact (hwder x hx).deriv
    exact ((hF2diff r hr).hasDerivAt.sub
      (farCandidateD1_hasDerivAt a b c r
        (ne_of_gt hr))).congr_of_eventuallyEq hEq
  have hodew : ∀ r : ℝ, 0 < r →
      deriv (deriv w) r + (n - 1) / r * deriv w r =
        g r := by
    intro r hr
    have hdif := radial_profile_barrier_difference n r
      (F r) (deriv F r) (deriv (deriv F) r)
      (q r) (q₁ r) (q₂ r) hr (hFode r hr)
    rw [(hwder₂ r hr).deriv, (hwder r hr).deriv]
    dsimp [g, e, κ, w]
    linear_combination hdif
  obtain ⟨R, hR⟩ := derivative_sixth_bound_of_scaled_ode
    (γ := n - 1) (by linarith) (fun r hr => (hwder r hr).differentiableAt)
    (fun r hr => (hwder₂ r hr).differentiableAt)
    hodew hwlim hglim
  refine ⟨R, ?_⟩
  intro r hrR hr
  have hbound := hR r hrR hr
  rw [(hwder r hr).deriv] at hbound
  simpa [q₁, a, b, c] using hbound

/-- The derivative of the sixth-order candidate has no terms at scale
`r⁵` beyond the fourth-order Laurent coefficient. -/
theorem farCandidateD1_scaled_fifth
    (a b c r : ℝ) (hr : r ≠ 0) :
    r ^ 5 * farCandidateD1 a b c r - 2 * a * r ^ 2 =
      -4 * b - 6 * c * r ^ (-2 : ℤ) := by
  unfold farCandidateD1
  simp only [zpow_neg]
  field_simp [hr]
  ring

/-- A sixth-order derivative bound is more than enough for the exact
fifth-order derivative limit used in the terminal sign computation. -/
theorem derivative_limit_of_sixth_order_bound
    {F : ℝ → ℝ} {a b c C R : ℝ}
    (_hC : 0 ≤ C)
    (hbound : ∀ r : ℝ, R ≤ r → 0 < r →
      |deriv F r - farCandidateD1 a b c r| ≤
        C * r ^ (-6 : ℤ)) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 5 * deriv F r - 2 * a * r ^ 2)
      Filter.atTop (𝓝 (-4 * b)) := by
  have hrema : Filter.Tendsto
      (fun r : ℝ => r ^ 5 *
        (deriv F r - farCandidateD1 a b c r))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    have hinv : Filter.Tendsto (fun r : ℝ => C * r⁻¹)
        Filter.atTop (𝓝 (0 : ℝ)) := by
      convert (tendsto_const_nhds (x := C)).mul
        tendsto_inv_atTop_zero using 1 <;> ring
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ r : ℝ in Filter.atTop, C * r⁻¹ < ε :=
      hinv.eventually (eventually_lt_nhds hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      ((Filter.eventually_ge_atTop R).and
        ((Filter.eventually_gt_atTop (0 : ℝ)).and hsmall))
    refine ⟨N, ?_⟩
    intro r hrN
    obtain ⟨hrR, hr, hsmallr⟩ := hN r hrN
    have h := hbound r hrR hr
    have htarget : |r ^ 5 * (deriv F r - farCandidateD1 a b c r)| ≤
        C * r⁻¹ := by
      rw [abs_mul, abs_of_pos (pow_pos hr 5)]
      calc
        r ^ 5 * |deriv F r - farCandidateD1 a b c r| ≤
            r ^ 5 * (C * (r ^ 6)⁻¹) := by
              simpa only [zpow_neg] using
                mul_le_mul_of_nonneg_left h (le_of_lt (pow_pos hr 5))
        _ = C * r⁻¹ := by field_simp [ne_of_gt hr] <;> ring
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt htarget hsmallr
  have htail : Filter.Tendsto
      (fun r : ℝ => -6 * c * r ^ (-2 : ℤ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := -6 * c)).mul
      invSquare_tendsto_zero using 1 <;> ring
  have hsum : Filter.Tendsto
      (fun r : ℝ => -4 * b +
        (r ^ 5 * (deriv F r - farCandidateD1 a b c r) +
          -6 * c * r ^ (-2 : ℤ)))
      Filter.atTop (𝓝 (-4 * b)) := by
    convert (tendsto_const_nhds (x := -4 * b)).add
      (hrema.add htail) using 1 <;> ring
  apply hsum.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
  have hq := farCandidateD1_scaled_fifth a b c r (ne_of_gt hr)
  nlinarith [hq]

/-- This is the terminal sign with an explicit derivative error estimate.
The estimate is exactly what the short-interval ODE interpolation must
produce from the sixth-order positional enclosure. -/
theorem infinityW_eventually_pos_of_sixth_derivative_bound
    (n : ℕ) {F : ℝ → ℝ} {C R : ℝ}
    (hn : 3 ≤ n) (hC : 0 ≤ C)
    (hU : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-infinityCoeff2 n)))
    (hV : Filter.Tendsto
      (fun r : ℝ => r ^ 4 * (F r - 1) +
        infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (infinityCoeff4 n)))
    (hbound : ∀ r : ℝ, R ≤ r → 0 < r →
      |deriv F r - farCandidateD1
        (infinityCoeff2 n) (infinityCoeff4 n)
        (farCoeff6Residual (n : ℝ) / 2) r| ≤
        C * r ^ (-6 : ℤ)) :
    ∀ᶠ r : ℝ in Filter.atTop, 0 < infinityW F r := by
  apply infinityW_eventually_pos n hn hU hV
  exact derivative_limit_of_sixth_order_bound hC hbound

/-- The far-field discrepancy is eventually positive for every smooth
radial ODE profile converging to one in dimension at least three.  The
derivative asymptotic is derived from the equation and the positional
Laurent enclosure inside this development. -/
theorem infinityW_eventually_pos_from_radial_ode
    (n : ℕ) {F : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt (n : ℝ) r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    ∀ᶠ r : ℝ in Filter.atTop, 0 < infinityW F r := by
  have hnreal : (1 : ℝ) ≤ n := by
    exact_mod_cast (by omega : 1 ≤ n)
  have hU : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-infinityCoeff2 n)) := by
    convert (radial_profile_first_coefficient hnreal hFone
      hFdiff hF2diff hFode) using 1
    unfold infinityCoeff2
    ring
  have hVraw := radial_profile_second_coefficient hnreal
    hFone hFdiff hF2diff hFode
  have hV : Filter.Tendsto
      (fun r : ℝ => r ^ 4 * (F r - 1) +
        infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (infinityCoeff4 n)) := by
    have hraw : Filter.Tendsto
        (fun r : ℝ => r ^ 4 *
          (F r - 1 + infinityCoeff2 n * r ^ (-2 : ℤ)))
        Filter.atTop (𝓝 (infinityCoeff4 n)) := by
      simpa [infinityCoeff2, infinityCoeff4] using hVraw
    apply hraw.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [zpow_neg]
    field_simp [ne_of_gt hr] <;> ring
  obtain ⟨R, hD⟩ := radial_profile_derivative_sixth_bound
    hnreal hFone hFdiff hF2diff hFode
  apply infinityW_eventually_pos_of_sixth_derivative_bound
    (C := 384) (R := R) n hn (by norm_num) hU hV
  intro r hrR hr
  simpa [infinityCoeff2, infinityCoeff4] using hD r hrR hr

end

end BrezisOP6
