import BrezisOP6.BridgeAnnularCoercivitySharp

/-! A prescribed profile-only angular coefficient controls the derivative
remainder for every spherical trace. -/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem bridgeQuadratic_controls_meanZero_radial_derivative_on_annulus_fixed
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc : ℝ → ℝ) (δ ρ R κ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ ≤ R)
    (he : ‖e‖ = 1)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ d r)
    (hdCont : ContinuousOn d (Icc δ ρ))
    (hdPos : ∀ r ∈ Icc δ ρ, 0 < d r)
    (hκ : 0 < κ)
    (hκBound : ∀ r ∈ Icc δ ρ, κ ≤ r ^ (m + 2) * d r)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc) volume 0 R)
    (hmeanNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m d c dc r)
    (hAlocal : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2)
        volume ε R)
    (hNormInt : IntervalIntegrable
      (fun r => ‖dv r - dc r • e‖ ^ 2) volume δ ρ) :
    κ * (∫ r in δ..ρ, ‖dv r - dc r • e‖ ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          bridgeQuadraticDensity m d v dv angular r := by
  let Q := bridgeQuadraticDensity m d v dv angular
  let M := bridgeMeanDensity m d c dc
  let A : ℝ → ℝ :=
    fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2
  let B : ℝ → ℝ :=
    fun r => r ^ m * d r *
      (angular r - (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2)
  have hR : 0 < R := lt_of_lt_of_le hδ (hδρ.trans hρR)
  have hpoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      Q r - M r = A r + B r := by
    have hp := bridgeQuadraticDensity_sub_mean_eq_remainder
      m e (v r) (dv r) r (d r) (c r) (dc r)
      (angular r) he (hv r hr) (hdv r hr)
    simpa only [Q, M, A, B, bridgeQuadraticDensity,
      bridgeMeanDensity] using hp
  have hBnonneg (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      0 ≤ B r := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (pow_nonneg hr.1 _) (hd r hr))
      (sub_nonneg.mpr (hgap r hr))
  have hApoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      A r ≤ Q r - M r := by
    linarith [hpoint r hr, hBnonneg r hr]
  have hdiffInt : IntervalIntegrable (fun r => Q r - M r) volume 0 R :=
    hfullInt.sub hmeanInt
  have hdiffLim := annular_integral_left_tendsto
    (fun r => Q r - M r) R hR hdiffInt
  have hEv : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (∫ r in δ..R, A r) ≤ ∫ r in ε..R, Q r - M r := by
    filter_upwards [Ioc_mem_nhdsGT hδ] with ε hε
    have hεR : ε ≤ R := hε.2.trans (hδρ.trans hρR)
    have hAε : IntervalIntegrable A volume ε R :=
      hAlocal ε hε.1 hεR
    have hdiffε : IntervalIntegrable (fun r => Q r - M r) volume ε R := by
      apply hdiffInt.mono_set
      rw [uIcc_of_le hεR, uIcc_of_le hR.le]
      intro r hr
      exact ⟨hε.1.le.trans hr.1, hr.2⟩
    have hsubset : (∫ r in δ..R, A r) ≤ ∫ r in ε..R, A r := by
      have hposAE : 0 ≤ᵐ[volume.restrict (Ioc ε R)] A := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        dsimp [A]
        exact mul_nonneg
          (mul_nonneg (pow_nonneg (hε.1.trans hr.1).le _)
            (hd r ⟨(hε.1.trans hr.1).le, hr.2⟩))
          (sq_nonneg _)
      exact intervalIntegral.integral_mono_interval
        hε.2 (hδρ.trans hρR) le_rfl hposAE hAε
    have hcomparison : (∫ r in ε..R, A r) ≤
        ∫ r in ε..R, Q r - M r := by
      apply intervalIntegral.integral_mono_on hεR hAε hdiffε
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) R := by
        exact ⟨hε.1.le.trans hr.1, hr.2⟩
      exact hApoint r hr'
    exact hsubset.trans hcomparison
  have hEvNeg : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      -(∫ r in ε..R, Q r - M r) ≤ -(∫ r in δ..R, A r) := by
    filter_upwards [hEv] with ε hε
    linarith
  have hlimNeg : Tendsto
      (fun ε : ℝ => -(∫ r in ε..R, Q r - M r))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(∫ r in (0 : ℝ)..R, Q r - M r))) := hdiffLim.neg
  have hAfullDiff : (∫ r in δ..R, A r) ≤
      ∫ r in (0 : ℝ)..R, Q r - M r := by
    have hlim := le_of_tendsto hlimNeg hEvNeg
    linarith
  have hAfull : (∫ r in δ..R, A r) ≤
      ∫ r in (0 : ℝ)..R, Q r := by
    rw [intervalIntegral.integral_sub hfullInt hmeanInt] at hAfullDiff
    linarith
  have hAδρ : IntervalIntegrable A volume δ ρ := by
    apply (hAlocal δ hδ (hδρ.trans hρR)).mono_set
    rw [uIcc_of_le hδρ, uIcc_of_le (hδρ.trans hρR)]
    intro r hr
    exact ⟨hr.1, hr.2.trans hρR⟩
  have hScaledInt : IntervalIntegrable
      (fun r => κ * ‖dv r - dc r • e‖ ^ 2) volume δ ρ :=
    hNormInt.const_mul κ
  have hscaledPoint : ∀ r ∈ Icc δ ρ,
      κ * ‖dv r - dc r • e‖ ^ 2 ≤ A r := by
    intro r hr
    exact mul_le_mul_of_nonneg_right (hκBound r hr) (sq_nonneg _)
  have hLower : κ * (∫ r in δ..ρ,
      ‖dv r - dc r • e‖ ^ 2) ≤ ∫ r in δ..ρ, A r := by
    simpa only [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_mono_on hδρ hScaledInt hAδρ hscaledPoint)
  have hAannulus : (∫ r in δ..ρ, A r) ≤ ∫ r in δ..R, A r := by
    have hAδR := hAlocal δ hδ (hδρ.trans hρR)
    have hAposδ : 0 ≤ᵐ[volume.restrict (Ioc δ R)] A := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      dsimp [A]
      exact mul_nonneg
        (mul_nonneg (pow_nonneg (hδ.trans hr.1).le _)
          (hd r ⟨(hδ.trans hr.1).le, hr.2⟩))
        (sq_nonneg _)
    exact intervalIntegral.integral_mono_interval
      le_rfl hδρ hρR hAposδ hAδR
  exact (hLower.trans hAannulus).trans hAfull


end

end BrezisOP6
