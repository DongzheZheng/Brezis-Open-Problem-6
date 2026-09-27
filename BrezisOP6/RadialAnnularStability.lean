import BrezisOP6.RadialTracePoincare

/-!
# Quantitative annular stability of a spherical trace

The regularized scalar mean `b(r) = r c(r)` and the mean-zero radial
derivative are controlled by different positive remainders of the exact
quadratic bridge.  This module combines their bounds with the outer trace
and a Hilbert-valued radial Poincaré inequality.  The resulting estimate
controls a whole annular `L²` distance, not only an equality case.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- If the Picone remainder controls the regularized mean and the bridge
remainder controls the mean-zero radial derivative, their sum controls the
distance of every trace from its fixed outer value.  This lemma isolates
the one-dimensional assembly; the two input inequalities are proved for
physical profiles in the Picone and bridge modules. -/
theorem annular_trace_l2_with_fixed_remainder_constants
    (e : H) (v dh : ℝ → H) (c b : ℝ → ℝ)
    (δ ρ R Q lam κ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ ≤ R)
    (hlam : 0 < lam) (hκ : 0 < κ)
    (he : ‖e‖ = 1) (hcR : c R = 0)
    (hb : ∀ r ∈ Icc δ ρ, b r = r * c r)
    (hcont : ContinuousOn (fun r => v r - c r • e) (Icc δ R))
    (hderiv : ∀ r ∈ Ioo δ R,
      HasDerivAt (fun s => v s - c s • e) (dh r) r)
    (hDNormInt : IntervalIntegrable (fun r => ‖dh r‖) volume δ R)
    (hDSqInt : IntervalIntegrable (fun r => ‖dh r‖ ^ 2) volume δ R)
    (hCInt : IntervalIntegrable (fun r => c r ^ 2) volume δ ρ)
    (hBInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hTraceInt : IntervalIntegrable
      (fun r => ‖v r - v R‖ ^ 2) volume δ ρ)
    (hTraceZeroInt : IntervalIntegrable
      (fun r => ‖(v R - c R • e) - (v r - c r • e)‖ ^ 2)
      volume δ ρ)
    (hZero : lam * (∫ r in δ..ρ, b r ^ 2) ≤ Q)
    (hRadial : κ * (∫ r in δ..R, ‖dh r‖ ^ 2) ≤ Q) :
    0 < 2 * (1 / (lam * δ ^ 2) +
      ((ρ - δ) * (R - δ)) / κ) ∧
    (∫ r in δ..ρ, ‖v r - v R‖ ^ 2) ≤
      2 * (1 / (lam * δ ^ 2) +
        ((ρ - δ) * (R - δ)) / κ) * Q := by
  let h : ℝ → H := fun r => v r - c r • e
  let L : ℝ := (ρ - δ) * (R - δ)
  let C : ℝ := 2 * (1 / (lam * δ ^ 2) + L / κ)
  have hδR : δ ≤ R := hδρ.trans hρR
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hlamδ : 0 < lam * δ ^ 2 := mul_pos hlam hδ2
  have hL : 0 ≤ L :=
    mul_nonneg (sub_nonneg.mpr hδρ) (sub_nonneg.mpr hδR)
  have hC : 0 < C := by
    dsimp [C]
    have hfirst : 0 < 1 / (lam * δ ^ 2) := div_pos (by norm_num) hlamδ
    have hsecond : 0 ≤ L / κ := div_nonneg hL hκ.le
    positivity
  have hCnonneg : 0 ≤ ∫ r in δ..ρ, c r ^ 2 := by
    apply intervalIntegral.integral_nonneg hδρ
    intro r _
    exact sq_nonneg _
  have hBnonneg : 0 ≤ ∫ r in δ..ρ, b r ^ 2 := by
    apply intervalIntegral.integral_nonneg hδρ
    intro r _
    exact sq_nonneg _
  have hDnonneg : 0 ≤ ∫ r in δ..R, ‖dh r‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg hδR
    intro r _
    exact sq_nonneg _
  have hQnonneg : 0 ≤ Q :=
    (mul_nonneg hlam.le hBnonneg).trans hZero
  have hPointC (r : ℝ) (hr : r ∈ Icc δ ρ) :
      δ ^ 2 * c r ^ 2 ≤ b r ^ 2 := by
    rw [hb r hr]
    have hrδ : δ ≤ r := hr.1
    have hr0 : 0 ≤ r := hδ.le.trans hrδ
    have hsq : δ ^ 2 ≤ r ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (c r))]
  have hCI : δ ^ 2 * (∫ r in δ..ρ, c r ^ 2) ≤
      ∫ r in δ..ρ, b r ^ 2 := by
    have hScaled : IntervalIntegrable (fun r => δ ^ 2 * c r ^ 2)
        volume δ ρ := hCInt.const_mul (δ ^ 2)
    simpa only [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_mono_on hδρ hScaled hBInt hPointC)
  have hMeanBound : (∫ r in δ..ρ, c r ^ 2) ≤
      Q / (lam * δ ^ 2) := by
    apply (le_div_iff₀ hlamδ).2
    calc
      (∫ r in δ..ρ, c r ^ 2) * (lam * δ ^ 2) =
          lam * (δ ^ 2 * ∫ r in δ..ρ, c r ^ 2) := by ring
      _ ≤ lam * (∫ r in δ..ρ, b r ^ 2) :=
        mul_le_mul_of_nonneg_left hCI hlam.le
      _ ≤ Q := hZero
  have hDerivativeBound : (∫ r in δ..R, ‖dh r‖ ^ 2) ≤ Q / κ := by
    apply (le_div_iff₀ hκ).2
    simpa only [mul_comm] using hRadial
  have hTracePoincare :
      (∫ r in δ..ρ, ‖h R - h r‖ ^ 2) ≤
        L * ∫ r in δ..R, ‖dh r‖ ^ 2 := by
    simpa only [h, L] using radial_trace_annular_l2_le_radial_energy
      h dh δ ρ R hδρ hρR hcont hderiv hDNormInt hDSqInt
        hTraceZeroInt
  have hTraceBound : (∫ r in δ..ρ, ‖h R - h r‖ ^ 2) ≤
      L * (Q / κ) :=
    hTracePoincare.trans
      (mul_le_mul_of_nonneg_left hDerivativeBound hL)
  have hPoint (r : ℝ) (hr : r ∈ Icc δ ρ) :
      ‖v r - v R‖ ^ 2 ≤
        2 * c r ^ 2 + 2 * ‖h R - h r‖ ^ 2 := by
    have hdecomp : v r - v R = c r • e + (h r - h R) := by
      dsimp [h]
      rw [hcR]
      simp only [zero_smul, sub_zero]
      abel
    have hnorm : ‖v r - v R‖ ≤ |c r| + ‖h R - h r‖ := by
      rw [hdecomp]
      calc
        ‖c r • e + (h r - h R)‖ ≤
            ‖c r • e‖ + ‖h r - h R‖ := norm_add_le _ _
        _ = |c r| + ‖h R - h r‖ := by
          rw [norm_smul, he, mul_one, norm_sub_rev]
          rfl
    have hnorm0 : 0 ≤ ‖v r - v R‖ := norm_nonneg _
    have habs0 : 0 ≤ |c r| := abs_nonneg _
    have hdiff0 : 0 ≤ ‖h R - h r‖ := norm_nonneg _
    nlinarith [sq_nonneg (|c r| - ‖h R - h r‖), sq_abs (c r)]
  have hTraceZeroInt' : IntervalIntegrable
      (fun r => ‖h R - h r‖ ^ 2) volume δ ρ := by
    simpa only [h] using hTraceZeroInt
  have hRHSInt : IntervalIntegrable
      (fun r => 2 * c r ^ 2 + 2 * ‖h R - h r‖ ^ 2)
      volume δ ρ :=
    (hCInt.const_mul 2).add (hTraceZeroInt'.const_mul 2)
  have hIntegral : (∫ r in δ..ρ, ‖v r - v R‖ ^ 2) ≤
      2 * (∫ r in δ..ρ, c r ^ 2) +
        2 * (∫ r in δ..ρ, ‖h R - h r‖ ^ 2) := by
    have hmono := intervalIntegral.integral_mono_on hδρ
      hTraceInt hRHSInt hPoint
    rw [intervalIntegral.integral_add
      (hCInt.const_mul 2) (hTraceZeroInt'.const_mul 2),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hmono
    exact hmono
  refine ⟨hC, ?_⟩
  calc
    (∫ r in δ..ρ, ‖v r - v R‖ ^ 2) ≤
        2 * (∫ r in δ..ρ, c r ^ 2) +
          2 * (∫ r in δ..ρ, ‖h R - h r‖ ^ 2) := hIntegral
    _ ≤ 2 * (Q / (lam * δ ^ 2)) + 2 * (L * (Q / κ)) := by
      gcongr
    _ = C * Q := by
      dsimp [C]
      ring

/-- The existential interface used by the original qualitative bridge
argument.  The preceding theorem keeps the constant explicit, so it can
be chosen once for every smooth competitor on the same annulus. -/
theorem annular_trace_l2_of_zero_mode_and_radial_remainders
    (e : H) (v dh : ℝ → H) (c b : ℝ → ℝ)
    (δ ρ R Q : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ ≤ R)
    (he : ‖e‖ = 1) (hcR : c R = 0)
    (hb : ∀ r ∈ Icc δ ρ, b r = r * c r)
    (hcont : ContinuousOn (fun r => v r - c r • e) (Icc δ R))
    (hderiv : ∀ r ∈ Ioo δ R,
      HasDerivAt (fun s => v s - c s • e) (dh r) r)
    (hDNormInt : IntervalIntegrable (fun r => ‖dh r‖) volume δ R)
    (hDSqInt : IntervalIntegrable (fun r => ‖dh r‖ ^ 2) volume δ R)
    (hCInt : IntervalIntegrable (fun r => c r ^ 2) volume δ ρ)
    (hBInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hTraceInt : IntervalIntegrable
      (fun r => ‖v r - v R‖ ^ 2) volume δ ρ)
    (hTraceZeroInt : IntervalIntegrable
      (fun r => ‖(v R - c R • e) - (v r - c r • e)‖ ^ 2)
      volume δ ρ)
    (hZero : ∃ lam : ℝ, 0 < lam ∧
      lam * (∫ r in δ..ρ, b r ^ 2) ≤ Q)
    (hRadial : ∃ κ : ℝ, 0 < κ ∧
      κ * (∫ r in δ..R, ‖dh r‖ ^ 2) ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      (∫ r in δ..ρ, ‖v r - v R‖ ^ 2) ≤ C * Q := by
  obtain ⟨lam, hlam, hZero⟩ := hZero
  obtain ⟨κ, hκ, hRadial⟩ := hRadial
  obtain ⟨hC, hbound⟩ :=
    annular_trace_l2_with_fixed_remainder_constants
      e v dh c b δ ρ R Q lam κ hδ hδρ hρR hlam hκ
      he hcR hb hcont hderiv hDNormInt hDSqInt hCInt hBInt
      hTraceInt hTraceZeroInt hZero hRadial
  exact ⟨2 * (1 / (lam * δ ^ 2) +
      ((ρ - δ) * (R - δ)) / κ), hC, hbound⟩

end

end BrezisOP6
