import BrezisOP6.ProfilePiconeEqualityInterior
import BrezisOP6.ProfileContactFromODE
import BrezisOP6.ProfilePiconeRemainderMeasurable

/-!
# Annular coercivity of the zero mode

The exact Picone identity is retained for near-minimizers, not merely for
the equality case.  On every fixed annulus, the full zero-mode quadratic
form controls the positive contact remainder.  This is the estimate needed
to pass zero-mode rigidity through a strongly convergent smooth sequence
without regularizing the weak minimizer by an elliptic equation.
-/

namespace BrezisOP6

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- A positive continuous weight has a uniform positive lower bound on a
closed annulus.  This elementary compactness step is stated explicitly
because it turns the Picone remainder into an `L²` estimate. -/
theorem positive_continuous_annular_weight_has_lower_bound
    (w : ℝ → ℝ) (δ ρ : ℝ) (hδρ : δ ≤ ρ)
    (hwcont : ContinuousOn w (Icc δ ρ))
    (hwpos : ∀ r ∈ Icc δ ρ, 0 < w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc δ ρ, c ≤ w r := by
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨δ, left_mem_Icc.mpr hδρ⟩ hwcont
  exact ⟨w r₀, hwpos r₀ hr₀, fun r hr => hmin hr⟩

/-- The physical coefficient `r^m h(r) S(r)` is uniformly positive on
every compact subannulus of the open ball.  The hypotheses are precisely
smooth profile regularity, positive profile separation, and strict contact
positivity; no uniform constant is supplied in advance. -/
theorem profilePicone_annular_coefficient_lower_bound
    (m : ℕ) (f F : ℝ → ℝ) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (hFpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < F r)
    (hMpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < profileM f F r)
    (hSpos : ∀ r ∈ Ioo (0 : ℝ) R,
      0 < profileContactResidual f F r) :
    ∃ c : ℝ, 0 < c ∧
      ∀ r ∈ Icc δ ρ,
        c ≤ profilePiconeRemainder m f F (fun _ => 1) r := by
  have hsubset : Icc δ ρ ⊆ Ioo (0 : ℝ) R := by
    intro r hr
    exact ⟨lt_of_lt_of_le hδ hr.1, lt_of_le_of_lt hr.2 hρR⟩
  have hcont : ContinuousOn
      (profilePiconeRemainder m f F (fun _ => 1))
      (Icc δ ρ) :=
    (profilePiconeRemainder_continuousOn_punctured
      m f F (fun _ => 1) R hfC1 hFC1
      hFpos hMpos continuousOn_const).mono hsubset
  have hpos : ∀ r ∈ Icc δ ρ,
      0 < profilePiconeRemainder m f F (fun _ => 1) r := by
    intro r hr
    have hr' := hsubset hr
    have hWeight := piconeWeight_pos f F r hr'.1
      (hFpos r hr') (hMpos r hr')
    have hContact := hSpos r hr'
    simpa only [profilePiconeRemainder, profileContactResidual,
      one_pow, mul_one] using
      mul_pos (mul_pos (pow_pos hr'.1 m) hWeight) hContact
  exact positive_continuous_annular_weight_has_lower_bound
    _ δ ρ hδρ hcont hpos

theorem annular_integral_left_tendsto
    (g : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hInt : IntervalIntegrable g volume 0 R) :
    Tendsto (fun δ : ℝ => ∫ r in δ..R, g r)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in (0 : ℝ)..R, g r)) := by
  have hcontRight : ContinuousOn (fun δ : ℝ => ∫ r in R..δ, g r)
      (Icc (0 : ℝ) R) := by
    simpa [uIcc_of_le hR.le] using
      (intervalIntegral.continuousOn_primitive_interval'
        hInt (show R ∈ uIcc (0 : ℝ) R by
          simpa [uIcc_of_le hR.le] using
            (Set.right_mem_Icc.mpr hR.le)))
  have hcontLeft : ContinuousOn (fun δ : ℝ => ∫ r in δ..R, g r)
      (Icc (0 : ℝ) R) := by
    convert hcontRight.neg using 1
    ext δ
    exact intervalIntegral.integral_symm R δ
  have hwithin : (𝓝[>] (0 : ℝ)) ≤
      (𝓝[Icc (0 : ℝ) R] (0 : ℝ)) :=
    nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT hR)
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) R := ⟨le_rfl, hR.le⟩
  exact (hcontLeft.continuousWithinAt h0mem).tendsto.mono_left hwithin

/-- The zero-mode energy controls its positive Picone remainder on every
annulus bounded away from the origin.  The coefficient in that remainder
is `r^m h(r) S(r)`, which is strictly positive for physical profiles.
The result is quantitative even when the energy is small but nonzero. -/
theorem profilePicone_zero_mode_controls_annular_remainder
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hMpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hSnonneg : ∀ r ∈ Ioc (0 : ℝ) R,
      0 ≤ profileContactResidual f F r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      volume 0 R)
    (hSqInt : IntervalIntegrable (profilePiconeSquare m f F b db)
      volume 0 R)
    (hRemInt : IntervalIntegrable (profilePiconeRemainder m f F b)
      volume 0 R)
    (hsq_int : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        volume ε R)
    (hflux_cont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F b)
        (uIcc ε R))
    (hflux_int : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        volume ε R)
    (hrem_int : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
        volume ε R)
    (hfactor : Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    (∫ r in δ..R, profilePiconeRemainder m f F b r) ≤
      ∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F b db r := by
  let D := profilePiconeDensity m f F b db
  let Sq := profilePiconeSquare m f F b db
  let Rem := profilePiconeRemainder m f F b
  let Flux := profilePiconeBoundaryFlux m f F b
  have hDlim := annular_integral_left_tendsto D R (lt_of_lt_of_le hδ hδR) hDint
  have hSqlim := annular_integral_left_tendsto Sq R (lt_of_lt_of_le hδ hδR) hSqInt
  have hRemlim := annular_integral_left_tendsto Rem R (lt_of_lt_of_le hδ hδR) hRemInt
  obtain ⟨B, hbRight⟩ := hblim
  have hFluxlim : Tendsto Flux (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    profilePiconeBoundaryFlux_tendsto_zero_of_right_limit
      m f F b R B (lt_of_lt_of_le hδ hδR)
      hFpos hMpos hfactor hbRight
  have hidentEvent :
      (fun ε : ℝ => ∫ r in ε..R, D r) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ =>
        (∫ r in ε..R, Sq r) - Flux ε +
          (∫ r in ε..R, Rem r)) := by
    filter_upwards [Ioc_mem_nhdsGT (lt_of_lt_of_le hδ hδR)] with ε hε
    have hsubset : uIcc ε R ⊆ Ioc (0 : ℝ) R := by
      intro r hr
      have hrI : r ∈ Icc ε R := by
        simpa [uIcc_of_le hε.2] using hr
      exact ⟨lt_of_lt_of_le hε.1 hrI.1, hrI.2⟩
    have hsubsetOpen : uIoo ε R ⊆ Ioo (0 : ℝ) R := by
      intro r hr
      have hrI : r ∈ Ioo ε R := by
        simpa [uIoo_of_le hε.2] using hr
      exact ⟨lt_trans hε.1 hrI.1, hrI.2⟩
    have hident := profilePicone_interval_interior
      m f F b db f₂ F₂ ε R hε.1 hε.2
      (fun r hr => hFpos r (hsubset hr))
      (fun r hr => hMpos r (hsubset hr))
      hfDiff hFDiff
      (fun r hr => hdf r (hsubsetOpen hr))
      (fun r hr => hdF r (hsubsetOpen hr))
      (fun r hr => hode_f r (hsubsetOpen hr))
      (fun r hr => hode_F r (hsubsetOpen hr))
      (fun r hr => hb r (hsubsetOpen hr))
      (hsq_int ε hε.1 hε.2)
      (hflux_cont ε hε.1 hε.2)
      (hflux_int ε hε.1 hε.2)
      (hrem_int ε hε.1 hε.2)
    have hOuter : Flux R = 0 := by
      simp [Flux, profilePiconeBoundaryFlux, hbR]
    change (∫ r in ε..R, D r) =
      (∫ r in ε..R, Sq r) + (Flux R - Flux ε) +
        (∫ r in ε..R, Rem r) at hident
    rw [hOuter] at hident
    simpa only [zero_sub, sub_eq_add_neg, zero_add] using hident
  have hRightLim : Tendsto
      (fun ε : ℝ =>
        (∫ r in ε..R, Sq r) - Flux ε +
          (∫ r in ε..R, Rem r))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ r in (0 : ℝ)..R, Sq r) +
        (∫ r in (0 : ℝ)..R, Rem r))) := by
    simpa only [sub_zero] using (hSqlim.sub hFluxlim).add hRemlim
  have hDidentity : (∫ r in (0 : ℝ)..R, D r) =
      (∫ r in (0 : ℝ)..R, Sq r) +
        (∫ r in (0 : ℝ)..R, Rem r) :=
    tendsto_nhds_unique
      ((tendsto_congr' hidentEvent).1 hDlim) hRightLim
  have hSqNonneg : 0 ≤ ∫ r in (0 : ℝ)..R, Sq r := by
    apply intervalIntegral.integral_nonneg (lt_of_lt_of_le hδ hδR).le
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hzero | hpos
    · subst r
      simp [Sq, profilePiconeSquare]
    · have hrc : r ∈ Ioc (0 : ℝ) R := ⟨hpos, hr.2⟩
      have hWeight := piconeWeight_pos f F r hpos
        (hFpos r hrc) (hMpos r hrc)
      have hPhi := piconeMultiplier_pos f F r hpos
        (hFpos r hrc) (hMpos r hrc)
      dsimp [Sq, profilePiconeSquare]
      positivity
  have hRemNonnegAE : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) R)] Rem := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hWeight := piconeWeight_pos f F r hr.1
      (hFpos r hr) (hMpos r hr)
    have hContact := hSnonneg r hr
    dsimp [Rem, profilePiconeRemainder,
      profileContactResidual, profileM, ratioM] at *
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg hr.1.le _) hWeight.le)
        hContact) (sq_nonneg (b r))
  have hAnnularLe : (∫ r in δ..R, Rem r) ≤
      ∫ r in (0 : ℝ)..R, Rem r :=
    intervalIntegral.integral_mono_interval
      (le_of_lt hδ) hδR le_rfl hRemNonnegAE hRemInt
  dsimp [D, Rem] at hDidentity hAnnularLe ⊢
  linarith

/-- A positive profile contact coefficient converts the annular Picone
remainder bound into a quantitative `L²` estimate.  The bound `hQ` is the
conclusion of `profilePicone_zero_mode_controls_annular_remainder`; it is
kept as an argument so the compactness step does not duplicate that
theorem's ODE and flux hypotheses. -/
theorem profilePicone_zero_mode_controls_annular_l2
    (m : ℕ) (f F b db : ℝ → ℝ) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (hFpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < F r)
    (hMpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < profileM f F r)
    (hSpos : ∀ r ∈ Ioo (0 : ℝ) R,
      0 < profileContactResidual f F r)
    (hBsqInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hRemInt : IntervalIntegrable (profilePiconeRemainder m f F b)
      volume δ R)
    (hRemNonneg : ∀ r ∈ Ioc δ R,
      0 ≤ profilePiconeRemainder m f F b r)
    (hQ : (∫ r in δ..R, profilePiconeRemainder m f F b r) ≤
      ∫ r in (0 : ℝ)..R, profilePiconeDensity m f F b db r) :
    ∃ c : ℝ, 0 < c ∧
      c * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          profilePiconeDensity m f F b db r := by
  obtain ⟨c, hc, hcBound⟩ :=
    profilePicone_annular_coefficient_lower_bound m f F δ ρ R
      hδ hδρ hρR hfC1 hFC1 hFpos hMpos hSpos
  refine ⟨c, hc, ?_⟩
  have hRemSubInt : IntervalIntegrable
      (profilePiconeRemainder m f F b) volume δ ρ := by
    apply hRemInt.mono_set
    simpa only [uIcc_of_le hδρ, uIcc_of_le (le_trans hδρ hρR.le)] using
      (Icc_subset_Icc le_rfl hρR.le)
  have hScaledInt : IntervalIntegrable (fun r => c * b r ^ 2)
      volume δ ρ := hBsqInt.const_mul c
  have hPoint : ∀ r ∈ Icc δ ρ,
      c * b r ^ 2 ≤ profilePiconeRemainder m f F b r := by
    intro r hr
    calc
      c * b r ^ 2 ≤
          profilePiconeRemainder m f F (fun _ => 1) r * b r ^ 2 :=
        mul_le_mul_of_nonneg_right (hcBound r hr) (sq_nonneg _)
      _ = profilePiconeRemainder m f F b r := by
        simp [profilePiconeRemainder]
  have hLower : c * (∫ r in δ..ρ, b r ^ 2) ≤
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

/-- The full profile/ODE version of annular zero-mode coercivity.  Unlike
the preceding compactness corollary, the zero-mode bound is established
inside this theorem from the Picone identity and the origin flux limit. -/
theorem profilePicone_zero_mode_annular_l2_from_profiles
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hMpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hSnonneg : ∀ r ∈ Ioc (0 : ℝ) R,
      0 ≤ profileContactResidual f F r)
    (hSpos : ∀ r ∈ Ioo (0 : ℝ) R,
      0 < profileContactResidual f F r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      volume 0 R)
    (hSqInt : IntervalIntegrable (profilePiconeSquare m f F b db)
      volume 0 R)
    (hRemInt : IntervalIntegrable (profilePiconeRemainder m f F b)
      volume 0 R)
    (hBsqInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hsq_int : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        volume ε R)
    (hflux_cont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F b)
        (uIcc ε R))
    (hflux_int : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        volume ε R)
    (hrem_int : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
        volume ε R)
    (hfactor : Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    ∃ c : ℝ, 0 < c ∧
      c * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          profilePiconeDensity m f F b db r := by
  have hδR : δ ≤ R := (hδρ.trans hρR.le)
  have hQ := profilePicone_zero_mode_controls_annular_remainder
    m f F b db f₂ F₂ δ R hδ hδR hFpos hMpos
    hfDiff hFDiff hdf hdF hode_f hode_F hb hSnonneg hbR
    hDint hSqInt hRemInt hsq_int hflux_cont hflux_int hrem_int
    hfactor hblim
  have hRemNonneg : ∀ r ∈ Ioc δ R,
      0 ≤ profilePiconeRemainder m f F b r := by
    intro r hr
    have hr' : r ∈ Ioc (0 : ℝ) R := ⟨lt_trans hδ hr.1, hr.2⟩
    have hWeight := piconeWeight_pos f F r hr'.1
      (hFpos r hr') (hMpos r hr')
    have hContact := hSnonneg r hr'
    dsimp [profilePiconeRemainder, profileContactResidual,
      profileM, ratioM] at *
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg hr'.1.le _) hWeight.le)
        hContact) (sq_nonneg (b r))
  exact profilePicone_zero_mode_controls_annular_l2
    m f F b db δ ρ R hδ hδρ hρR hfC1 hFC1
    (fun r hr => hFpos r ⟨hr.1, hr.2.le⟩)
    (fun r hr => hMpos r ⟨hr.1, hr.2.le⟩)
    hSpos hBsqInt (hrem_int δ hδ hδR) hRemNonneg hQ

end

end BrezisOP6
