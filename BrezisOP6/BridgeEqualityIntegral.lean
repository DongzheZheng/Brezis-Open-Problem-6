import BrezisOP6.BridgeEquality

/-!
# Equality in the integrated spherical bridge

The complete quadratic bridge and the zero mode are integrable.  Their
difference is the sum of two pointwise nonnegative remainders.  At equality,
the difference vanishes almost everywhere, so both remainders vanish almost
everywhere.  Separate integrability of the two remainders is unnecessary.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem bridgeQuadratic_integral_nonneg_of_mean_nonneg
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (he : ‖e‖ = 1)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ d r)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc) volume 0 R)
    (hmeanNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m d c dc r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeQuadraticDensity m d v dv angular r := by
  have hdiff : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeQuadraticDensity m d v dv angular r -
        bridgeMeanDensity m d c dc r := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) R := by
      simpa only [uIcc_of_le hR] using hr
    exact bridgeQuadraticDensity_sub_mean_nonneg m e (v r) (dv r)
      r (d r) (c r) (dc r) (angular r) hr'.1
      (hd r hr') he (hv r hr') (hdv r hr') (hgap r hr')
  rw [intervalIntegral.integral_sub hfullInt hmeanInt] at hdiff
  linarith

theorem bridgeQuadratic_zero_forces_remainders_zero_ae
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (he : ‖e‖ = 1)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ d r)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc) volume 0 R)
    (hmeanNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m d c dc r)
    (hfullZero : (∫ r in (0 : ℝ)..R,
      bridgeQuadraticDensity m d v dv angular r) = 0) :
    (∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m d c dc r) = 0 ∧
    (∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) R)),
      r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2 = 0 ∧
      r ^ m * d r *
        (angular r - (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2) = 0) := by
  let Q : ℝ → ℝ := bridgeQuadraticDensity m d v dv angular
  let M : ℝ → ℝ := bridgeMeanDensity m d c dc
  let A : ℝ → ℝ :=
    fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2
  let B : ℝ → ℝ :=
    fun r => r ^ m * d r *
      (angular r - (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2)
  have hpoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      Q r - M r = A r + B r := by
    have h := bridgeQuadraticDensity_sub_mean_eq_remainder
      m e (v r) (dv r) r (d r) (c r) (dc r)
      (angular r) he (hv r hr) (hdv r hr)
    simpa only [Q, M, A, B, bridgeQuadraticDensity,
      bridgeMeanDensity] using h
  have hApos (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      0 ≤ A r := by
    have hr0 : 0 ≤ r := hr.1
    have hdr : 0 ≤ d r := hd r hr
    dsimp [A]
    positivity
  have hBpos (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      0 ≤ B r := by
    have hr0 : 0 ≤ r := hr.1
    have hdr : 0 ≤ d r := hd r hr
    have hg := hgap r hr
    dsimp [B]
    exact mul_nonneg (mul_nonneg (pow_nonneg hr0 _) hdr)
      (sub_nonneg.mpr hg)
  have hdiffNonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) R)]
      (fun r => Q r - M r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hpoint r ⟨le_of_lt hr.1, hr.2⟩).symm ▸
      add_nonneg (hApos r ⟨le_of_lt hr.1, hr.2⟩)
        (hBpos r ⟨le_of_lt hr.1, hr.2⟩)
  have hdiffInt : IntervalIntegrable (fun r => Q r - M r)
      volume 0 R := hfullInt.sub hmeanInt
  change 0 ≤ ∫ r in (0 : ℝ)..R, M r at hmeanNonneg
  change (∫ r in (0 : ℝ)..R, Q r) = 0 at hfullZero
  have hmeanZero : (∫ r in (0 : ℝ)..R, M r) = 0 := by
    have hdiffIntegral : 0 ≤ ∫ r in (0 : ℝ)..R, Q r - M r := by
      rw [intervalIntegral.integral_of_le hR]
      exact integral_nonneg_of_ae hdiffNonneg
    rw [intervalIntegral.integral_sub hfullInt hmeanInt] at hdiffIntegral
    linarith
  have hdiffIntegralZero :
      (∫ r in (0 : ℝ)..R, Q r - M r) = 0 := by
    rw [intervalIntegral.integral_sub hfullInt hmeanInt]
    simpa [Q, M, hfullZero, hmeanZero]
  have hdiffZero : (fun r => Q r - M r) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      hR hdiffNonneg hdiffInt).mp hdiffIntegralZero
  constructor
  · exact hmeanZero
  filter_upwards [hdiffZero, ae_restrict_mem measurableSet_Ioc] with r hz hr
  change Q r - M r = 0 at hz
  have hr' : r ∈ Icc (0 : ℝ) R := ⟨le_of_lt hr.1, hr.2⟩
  have hp := hpoint r hr'
  have ha := hApos r hr'
  have hb := hBpos r hr'
  change A r = 0 ∧ B r = 0
  constructor <;> linarith

end

end BrezisOP6
