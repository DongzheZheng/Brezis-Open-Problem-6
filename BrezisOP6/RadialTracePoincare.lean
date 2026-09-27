import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import BrezisOP6.BridgeAnnularCoercivity

/-!
# A quantitative Hilbert-valued radial trace estimate

For a differentiable radial family, the distance between two spherical
`L²` traces is bounded by the integral of the radial speed.  Young's
inequality then bounds that distance in terms of the square-speed energy.
Combined with `BridgeAnnularCoercivity`, this is the one-dimensional
step that makes a near-minimizing bridge control its mean-zero trace
relative to a fixed boundary slice.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The Hilbert-valued radial fundamental theorem, with the derivative
represented by an explicit function `dh`. -/
theorem radial_trace_norm_sub_le_integral_speed
    (h dh : ℝ → H) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn h (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt h (dh t) t)
    (hNormInt : IntervalIntegrable (fun t => ‖dh t‖) volume a b) :
    ‖h b - h a‖ ≤ ∫ t in a..b, ‖dh t‖ := by
  apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hcont
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
  · filter_upwards [] with t
    intro ht
    rw [(hderiv t ht).deriv]
  · exact hNormInt

/-- A near-minimizer estimate that uses only the squared radial speed.
The free parameter `τ>0` allows a sequence with vanishing energy to
force its fixed-annulus trace distance to vanish. -/
theorem radial_trace_distance_young_bound
    (h dh : ℝ → H) (a b τ : ℝ) (hab : a ≤ b) (hτ : 0 < τ)
    (hcont : ContinuousOn h (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt h (dh t) t)
    (hNormInt : IntervalIntegrable (fun t => ‖dh t‖) volume a b)
    (hSqInt : IntervalIntegrable (fun t => ‖dh t‖ ^ 2) volume a b) :
    2 * τ * ‖h b - h a‖ ≤
      τ ^ 2 * (b - a) + ∫ t in a..b, ‖dh t‖ ^ 2 := by
  have hSpeed := radial_trace_norm_sub_le_integral_speed
    h dh a b hab hcont hderiv hNormInt
  have hPoint : ∀ t ∈ Icc a b,
      2 * τ * ‖dh t‖ ≤ τ ^ 2 + ‖dh t‖ ^ 2 := by
    intro t _
    nlinarith [sq_nonneg (‖dh t‖ - τ)]
  have hLeftInt : IntervalIntegrable (fun t => 2 * τ * ‖dh t‖)
      volume a b := hNormInt.const_mul (2 * τ)
  have hRightInt : IntervalIntegrable
      (fun t => τ ^ 2 + ‖dh t‖ ^ 2) volume a b :=
    (intervalIntegrable_const).add hSqInt
  have hIntegral : (∫ t in a..b, 2 * τ * ‖dh t‖) ≤
      ∫ t in a..b, τ ^ 2 + ‖dh t‖ ^ 2 :=
    intervalIntegral.integral_mono_on hab hLeftInt hRightInt hPoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) hSqInt,
    intervalIntegral.integral_const] at hIntegral
  simp only [smul_eq_mul] at hIntegral
  have hτ0 : 0 ≤ 2 * τ := by linarith
  nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hSpeed)]

/-- Optimizing the free parameter in the preceding Young estimate gives
the squared one-dimensional Poincaré inequality.  No external Sobolev
inequality is used: the estimate follows from the radial FTC and a
single elementary optimization. -/
theorem radial_trace_distance_sq_le_length_mul_energy
    (h dh : ℝ → H) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn h (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt h (dh t) t)
    (hNormInt : IntervalIntegrable (fun t => ‖dh t‖) volume a b)
    (hSqInt : IntervalIntegrable (fun t => ‖dh t‖ ^ 2) volume a b) :
    ‖h b - h a‖ ^ 2 ≤
      (b - a) * ∫ t in a..b, ‖dh t‖ ^ 2 := by
  let D : ℝ := ‖h b - h a‖
  let L : ℝ := b - a
  let E : ℝ := ∫ t in a..b, ‖dh t‖ ^ 2
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  have hE : 0 ≤ E := by
    dsimp [E]
    apply intervalIntegral.integral_nonneg hab
    intro t _
    exact sq_nonneg _
  by_cases hL0 : L = 0
  · have habEq : a = b := by
      dsimp [L] at hL0
      linarith
    subst b
    simp [D, L]
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
  by_cases hD0 : D = 0
  · change D ^ 2 ≤ L * E
    simpa [hD0] using (mul_nonneg hL hE)
  have hDpos : 0 < D := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD0)
  let τ : ℝ := D / L
  have hτ : 0 < τ := div_pos hDpos hLpos
  have hYoung := radial_trace_distance_young_bound
    h dh a b τ hab hτ hcont hderiv hNormInt hSqInt
  change 2 * τ * D ≤ τ ^ 2 * L + E at hYoung
  have hleft : 2 * τ * D = 2 * (D ^ 2 / L) := by
    dsimp [τ]
    ring
  have hright : τ ^ 2 * L = D ^ 2 / L := by
    dsimp [τ]
    field_simp [hL0] <;> ring
  rw [hleft, hright] at hYoung
  have hDiv : D ^ 2 / L ≤ E := by linarith
  have hFinal := (div_le_iff₀ hLpos).mp hDiv
  simpa only [D, L, E, mul_comm] using hFinal

/-- A fixed outer trace controls the squared `L²` distance of every
radial slice on an annulus.  The explicit constant is
`(ρ-δ)(R-δ)`; no harmonic-degree decomposition occurs here. -/
theorem radial_trace_annular_l2_le_radial_energy
    (h dh : ℝ → H) (δ ρ R : ℝ)
    (hδρ : δ ≤ ρ) (hρR : ρ ≤ R)
    (hcont : ContinuousOn h (Icc δ R))
    (hderiv : ∀ t ∈ Ioo δ R, HasDerivAt h (dh t) t)
    (hNormInt : IntervalIntegrable (fun t => ‖dh t‖) volume δ R)
    (hSqInt : IntervalIntegrable (fun t => ‖dh t‖ ^ 2) volume δ R)
    (hTraceInt : IntervalIntegrable
      (fun r => ‖h R - h r‖ ^ 2) volume δ ρ) :
    (∫ r in δ..ρ, ‖h R - h r‖ ^ 2) ≤
      (ρ - δ) * (R - δ) *
        ∫ t in δ..R, ‖dh t‖ ^ 2 := by
  let E : ℝ := ∫ t in δ..R, ‖dh t‖ ^ 2
  have hδR : δ ≤ R := hδρ.trans hρR
  have hE : 0 ≤ E := by
    dsimp [E]
    apply intervalIntegral.integral_nonneg hδR
    intro t _
    exact sq_nonneg _
  have hSqAE : 0 ≤ᵐ[volume.restrict (Ioc δ R)]
      (fun t => ‖dh t‖ ^ 2) :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have hPoint (r : ℝ) (hr : r ∈ Icc δ ρ) :
      ‖h R - h r‖ ^ 2 ≤ (R - δ) * E := by
    have hrR : r ≤ R := hr.2.trans hρR
    have hsub : uIcc r R ⊆ uIcc δ R := by
      intro t ht
      have ht' : t ∈ Icc r R := by
        simpa only [uIcc_of_le hrR] using ht
      simpa only [uIcc_of_le hδR] using
        (show t ∈ Icc δ R from ⟨hr.1.trans ht'.1, ht'.2⟩)
    have hcont' : ContinuousOn h (Icc r R) := by
      apply hcont.mono
      intro t ht
      exact ⟨hr.1.trans ht.1, ht.2⟩
    have hderiv' : ∀ t ∈ Ioo r R, HasDerivAt h (dh t) t := by
      intro t ht
      exact hderiv t ⟨lt_of_le_of_lt hr.1 ht.1, ht.2⟩
    have hNormInt' : IntervalIntegrable (fun t => ‖dh t‖)
        volume r R := hNormInt.mono_set hsub
    have hSqInt' : IntervalIntegrable (fun t => ‖dh t‖ ^ 2)
        volume r R := hSqInt.mono_set hsub
    have hRemainder := radial_trace_distance_sq_le_length_mul_energy
      h dh r R hrR hcont' hderiv' hNormInt' hSqInt'
    have hEsub : (∫ t in r..R, ‖dh t‖ ^ 2) ≤ E :=
      intervalIntegral.integral_mono_interval
        hr.1 hrR le_rfl hSqAE hSqInt
    have hEsubNonneg : 0 ≤ ∫ t in r..R, ‖dh t‖ ^ 2 := by
      apply intervalIntegral.integral_nonneg hrR
      intro t _
      exact sq_nonneg _
    calc
      ‖h R - h r‖ ^ 2 ≤
          (R - r) * ∫ t in r..R, ‖dh t‖ ^ 2 := hRemainder
      _ ≤ (R - δ) * ∫ t in r..R, ‖dh t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hr.1]) hEsubNonneg
      _ ≤ (R - δ) * E :=
        mul_le_mul_of_nonneg_left hEsub (sub_nonneg.mpr hδR)
  have hConstInt : IntervalIntegrable (fun _ : ℝ => (R - δ) * E)
      volume δ ρ := intervalIntegrable_const
  have hIntegral :
      (∫ r in δ..ρ, ‖h R - h r‖ ^ 2) ≤
        ∫ _r in δ..ρ, (R - δ) * E :=
    intervalIntegral.integral_mono_on hδρ hTraceInt hConstInt hPoint
  rw [intervalIntegral.integral_const] at hIntegral
  simp only [smul_eq_mul] at hIntegral
  nlinarith [hIntegral]

end

end BrezisOP6
