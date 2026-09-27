import BrezisOP6.BridgeAnnularCoercivitySharp

/-!
# Local integrability of the angular bridge remainder

On a positive-radius interval the radial derivative is continuous in the
spherical Hilbert space.  The nonnegative mean-zero remainder is bounded
by the difference between the complete bridge and its scalar mean.
Hence their integrability down to the origin automatically yields the
remainder's integrability on every punctured interval.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem bridgeRadialRemainder_intervalIntegrable_of_full_and_mean
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (he : ‖e‖ = 1)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ d r)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hdCont : ContinuousOn d (Ioo (0 : ℝ) R))
    (hdvCont : ContinuousOn dv (Ioo (0 : ℝ) R))
    (hdcCont : ContinuousOn dc (Ioo (0 : ℝ) R))
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc) volume 0 R) :
    ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2)
        volume ε R := by
  let Q := bridgeQuadraticDensity m d v dv angular
  let M := bridgeMeanDensity m d c dc
  let A : ℝ → ℝ :=
    fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2
  have hpoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      A r ≤ Q r - M r := by
    have hp := bridgeQuadraticDensity_sub_mean_eq_remainder
      m e (v r) (dv r) r (d r) (c r) (dc r)
      (angular r) he (hv r hr) (hdv r hr)
    have hEq : Q r - M r = A r +
        r ^ m * d r *
          (angular r - (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2) := by
      simpa only [Q, M, A, bridgeQuadraticDensity,
        bridgeMeanDensity] using hp
    have hB : 0 ≤ r ^ m * d r *
        (angular r - (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2) :=
      mul_nonneg
        (mul_nonneg (pow_nonneg hr.1 _) (hd r hr))
        (sub_nonneg.mpr (hgap r hr))
    linarith [hEq]
  intro ε hε hεR
  have hdiffInt : IntervalIntegrable (fun r => Q r - M r)
      volume ε R := by
    apply (hfullInt.sub hmeanInt).mono_set
    rw [uIcc_of_le hεR, uIcc_of_le hR.le]
    intro r hr
    exact ⟨hε.le.trans hr.1, hr.2⟩
  have hACont : ContinuousOn A (Ioo ε R) := by
    have hsub : Ioo ε R ⊆ Ioo (0 : ℝ) R := by
      intro r hr
      exact ⟨hε.trans hr.1, hr.2⟩
    have hDiff : ContinuousOn
        (fun r => dv r - dc r • e) (Ioo ε R) :=
      (hdvCont.mono hsub).sub
        ((hdcCont.mono hsub).smul continuousOn_const)
    dsimp only [A]
    exact (((continuousOn_id.pow (m + 2)).mul
      (hdCont.mono hsub)).mul (hDiff.norm.pow 2))
  have hAmeas : AEStronglyMeasurable A
      (volume.restrict (Ioc ε R)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hACont.aestronglyMeasurable measurableSet_Ioo
  have hdiffOn : Integrable (fun r => Q r - M r)
      (volume.restrict (Ioc ε R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hεR).mp hdiffInt
  have hAOn : Integrable A (volume.restrict (Ioc ε R)) := by
    apply Integrable.mono' hdiffOn hAmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r ∈ Icc (0 : ℝ) R :=
      ⟨(hε.trans hr.1).le, hr.2⟩
    have hA0 : 0 ≤ A r := by
      dsimp [A]
      exact mul_nonneg
        (mul_nonneg (pow_nonneg (hε.trans hr.1).le _)
          (hd r hr')) (sq_nonneg _)
    have hAM := hpoint r hr'
    have hM0 : 0 ≤ Q r - M r := hA0.trans hAM
    simpa only [Real.norm_eq_abs, abs_of_nonneg hA0,
      abs_of_nonneg hM0] using hAM
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hεR).mpr hAOn

end

end BrezisOP6
