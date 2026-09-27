import BrezisOP6.PhysicalRadialZeroModeAnnular

/-!
# Profile-only constants for annular Picone coercivity

The contact coefficient is determined by the two radial profiles and the
annulus.  Fixing its lower bound before selecting a competitor is necessary
for quantitative stability of a sequence of competitors.
-/

namespace BrezisOP6

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- A prescribed lower bound for the Picone contact coefficient gives the
same lower bound for the zero-mode quadratic form. -/
theorem profilePicone_zero_mode_controls_annular_l2_fixed
    (m : ℕ) (f F b db : ℝ → ℝ) (δ ρ R lam : ℝ)
    (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (hlam : 0 < lam)
    (hBound : ∀ r ∈ Icc δ ρ,
      lam ≤ profilePiconeRemainder m f F (fun _ => 1) r)
    (hBsqInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hRemInt : IntervalIntegrable (profilePiconeRemainder m f F b)
      volume δ R)
    (hRemNonneg : ∀ r ∈ Ioc δ R,
      0 ≤ profilePiconeRemainder m f F b r)
    (hQ : (∫ r in δ..R, profilePiconeRemainder m f F b r) ≤
      ∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F b db r) :
    lam * (∫ r in δ..ρ, b r ^ 2) ≤
      ∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F b db r := by
  have hRemSubInt : IntervalIntegrable
      (profilePiconeRemainder m f F b) volume δ ρ := by
    apply hRemInt.mono_set
    simpa only [uIcc_of_le hδρ, uIcc_of_le (le_trans hδρ hρR.le)] using
      (Icc_subset_Icc le_rfl hρR.le)
  have hScaledInt : IntervalIntegrable (fun r => lam * b r ^ 2)
      volume δ ρ := hBsqInt.const_mul lam
  have hPoint : ∀ r ∈ Icc δ ρ,
      lam * b r ^ 2 ≤ profilePiconeRemainder m f F b r := by
    intro r hr
    calc
      lam * b r ^ 2 ≤
          profilePiconeRemainder m f F (fun _ => 1) r * b r ^ 2 :=
        mul_le_mul_of_nonneg_right (hBound r hr) (sq_nonneg _)
      _ = profilePiconeRemainder m f F b r := by
        simp [profilePiconeRemainder]
  have hLower : lam * (∫ r in δ..ρ, b r ^ 2) ≤
      ∫ r in δ..ρ, profilePiconeRemainder m f F b r := by
    simpa only [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_mono_on hδρ hScaledInt hRemSubInt hPoint)
  have hRemNonnegAE :
      0 ≤ᵐ[volume.restrict (Ioc δ R)]
        profilePiconeRemainder m f F b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hRemNonneg r hr
  have hUpper : (∫ r in δ..ρ,
      profilePiconeRemainder m f F b r) ≤
      ∫ r in δ..R, profilePiconeRemainder m f F b r :=
    intervalIntegral.integral_mono_interval
      le_rfl hδρ hρR.le hRemNonnegAE hRemInt
  exact (hLower.trans hUpper).trans hQ

/-- Both constants are chosen from the profile data, before any scalar
mean or sphere coordinate is selected. -/
theorem PhysicalRadialData.annular_remainder_constant
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ r ∈ Icc δ ρ,
        lam ≤ profilePiconeRemainder m p.f p.F (fun _ => 1) r := by
  obtain ⟨hM, _, hS, _⟩ := p.contact_coercivity_certificate m R
  exact profilePicone_annular_coefficient_lower_bound
    m p.f p.F δ ρ R hδ hδρ hρR
    (p.hfC2.of_le (by norm_num)) (p.hFC2.of_le (by norm_num))
    (fun r hr => p.hFposAll r hr.1)
    (fun r hr => hM r ⟨hr.1, hr.2.le⟩) hS

/-- The angular radial weight is positive on the full closed annulus. -/
theorem PhysicalRadialData.annular_angular_constant
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (δ : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ r ∈ Icc δ R,
        κ ≤ r ^ (m + 2) * (p.f r ^ 2 - p.F r ^ 2) := by
  have hcont : ContinuousOn
      (fun r => r ^ (m + 2) * (p.f r ^ 2 - p.F r ^ 2))
      (Icc δ R) :=
    (continuousOn_id.pow (m + 2)).mul
      (((p.hfC2.continuous.pow 2).sub
        (p.hFC2.continuous.pow 2)).continuousOn)
  have hpos : ∀ r ∈ Icc δ R,
      0 < r ^ (m + 2) * (p.f r ^ 2 - p.F r ^ 2) := by
    intro r hr
    exact mul_pos (pow_pos (lt_of_lt_of_le hδ hr.1) _)
      (p.profile_gap_positive m R r
        ⟨lt_of_lt_of_le hδ hr.1, hr.2⟩)
  exact positive_continuous_annular_weight_has_lower_bound
    _ δ R hδR hcont hpos

end

end BrezisOP6
