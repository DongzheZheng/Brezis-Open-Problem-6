import BrezisOP6.ZeroModeEndpointInterior

/-!
# Equality in the finite-ball zero-mode Picone inequality

The pointwise contact residual is strictly positive in the open ball.
If the radial zero-mode energy vanishes, the Picone identity forces its
nonnegative remainder to have zero integral.  Almost-everywhere vanishing
of that remainder makes the zero mode vanish almost everywhere; the
mode's interior differentiability upgrades this to pointwise vanishing.

This module asks for integrability of the square and remainder down to
the origin.  Those endpoint hypotheses are separate from the annular
FTC assumptions and can be checked from the regular-origin expansions of
the actual smooth test field.
-/

namespace BrezisOP6

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

private theorem interval_integral_left_tendsto_of_integrable
    (g : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hInt : IntervalIntegrable g MeasureTheory.volume 0 R) :
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

theorem profilePicone_zero_mode_eq_zero_implies_mode_zero_interior
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
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
      0 ≤ contactResidual r (profileT F r) (profileY F r)
        (profileK f F r ^ 2 - 1) (profileEta f F r))
    (hSpos : ∀ r ∈ Ioo (0 : ℝ) R,
      0 < contactResidual r (profileT F r) (profileY F r)
        (profileK f F r ^ 2 - 1) (profileEta f F r))
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      volume 0 R)
    (hSqInt : IntervalIntegrable (profilePiconeSquare m f F b db)
      volume 0 R)
    (hRemInt : IntervalIntegrable (profilePiconeRemainder m f F b)
      volume 0 R)
    (hsq_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        volume δ R)
    (hflux_cont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F b)
        (uIcc δ R))
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        volume δ R)
    (hrem_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
        volume δ R)
    (hfactor : Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B))
    (hDzero : (∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r) = 0) :
    ∀ r ∈ Ioo (0 : ℝ) R, b r = 0 := by
  let D := profilePiconeDensity m f F b db
  let Sq := profilePiconeSquare m f F b db
  let Rem := profilePiconeRemainder m f F b
  let Flux := profilePiconeBoundaryFlux m f F b
  have hDlim := interval_integral_left_tendsto_of_integrable D R hR hDint
  have hSqlim := interval_integral_left_tendsto_of_integrable Sq R hR hSqInt
  have hRemlim := interval_integral_left_tendsto_of_integrable Rem R hR hRemInt
  obtain ⟨B, hbRight⟩ := hblim
  have hFluxlim : Tendsto Flux (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    profilePiconeBoundaryFlux_tendsto_zero_of_right_limit
      m f F b R B hR hFpos hMpos hfactor hbRight
  have hidentEvent :
      (fun δ : ℝ => ∫ r in δ..R, D r) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ =>
        (∫ r in δ..R, Sq r) - Flux δ +
          (∫ r in δ..R, Rem r)) := by
    filter_upwards [Ioc_mem_nhdsGT hR] with δ hδ
    have hsubset : uIcc δ R ⊆ Ioc (0 : ℝ) R := by
      intro r hr
      have hrI : r ∈ Icc δ R := by
        simpa [uIcc_of_le hδ.2] using hr
      exact ⟨lt_of_lt_of_le hδ.1 hrI.1, hrI.2⟩
    have hsubsetOpen : uIoo δ R ⊆ Ioo (0 : ℝ) R := by
      intro r hr
      have hrI : r ∈ Ioo δ R := by
        simpa [uIoo_of_le hδ.2] using hr
      exact ⟨lt_trans hδ.1 hrI.1, hrI.2⟩
    have hident := profilePicone_interval_interior
      m f F b db f₂ F₂ δ R hδ.1 hδ.2
      (fun r hr => hFpos r (hsubset hr))
      (fun r hr => hMpos r (hsubset hr))
      hfDiff hFDiff
      (fun r hr => hdf r (hsubsetOpen hr))
      (fun r hr => hdF r (hsubsetOpen hr))
      (fun r hr => hode_f r (hsubsetOpen hr))
      (fun r hr => hode_F r (hsubsetOpen hr))
      (fun r hr => hb r (hsubsetOpen hr))
      (hsq_int δ hδ.1 hδ.2)
      (hflux_cont δ hδ.1 hδ.2)
      (hflux_int δ hδ.1 hδ.2)
      (hrem_int δ hδ.1 hδ.2)
    have hOuter : Flux R = 0 := by
      simp [Flux, profilePiconeBoundaryFlux, hbR]
    change (∫ r in δ..R, D r) =
      (∫ r in δ..R, Sq r) + (Flux R - Flux δ) +
        (∫ r in δ..R, Rem r) at hident
    rw [hOuter] at hident
    simpa only [zero_sub, sub_eq_add_neg, zero_add] using hident
  have hRightLim : Tendsto
      (fun δ : ℝ =>
        (∫ r in δ..R, Sq r) - Flux δ +
          (∫ r in δ..R, Rem r))
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
    apply intervalIntegral.integral_nonneg hR.le
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
  have hRemNonneg : 0 ≤ ∫ r in (0 : ℝ)..R, Rem r := by
    apply intervalIntegral.integral_nonneg hR.le
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hzero | hpos
    · subst r
      simp [Rem, profilePiconeRemainder,
        piconeWeightFromProfiles]
    · have hrc : r ∈ Ioc (0 : ℝ) R := ⟨hpos, hr.2⟩
      have hWeight := piconeWeight_pos f F r hpos
        (hFpos r hrc) (hMpos r hrc)
      have hContact := hSnonneg r hrc
      dsimp [Rem, profilePiconeRemainder]
      positivity
  have hRemZero : (∫ r in (0 : ℝ)..R, Rem r) = 0 := by
    dsimp [D] at hDidentity hDzero
    linarith
  have hRemNonnegAE : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) R)] Rem := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hWeight := piconeWeight_pos f F r hr.1
      (hFpos r hr) (hMpos r hr)
    have hContact := hSnonneg r hr
    dsimp [Rem, profilePiconeRemainder]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg hr.1.le _) hWeight.le)
        hContact) (sq_nonneg (b r))
  have hRemAE : Rem =ᵐ[volume.restrict (Ioc (0 : ℝ) R)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      hR.le hRemNonnegAE hRemInt).mp hRemZero
  have hRemAEOpen : Rem =ᵐ[volume.restrict (Ioo (0 : ℝ) R)] 0 :=
    ae_restrict_of_ae_restrict_of_subset
      (by intro r hr; exact ⟨hr.1, hr.2.le⟩) hRemAE
  have hbAEOpen : b =ᵐ[volume.restrict (Ioo (0 : ℝ) R)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hRemAEOpen, ae_restrict_mem measurableSet_Ioo]
      with r hRem0 hr
    have hrc : r ∈ Ioc (0 : ℝ) R := ⟨hr.1, hr.2.le⟩
    have hWeight := piconeWeight_pos f F r hr.1
      (hFpos r hrc) (hMpos r hrc)
    have hContactPos := hSpos r hr
    have hcoef : 0 < r ^ m * piconeWeightFromProfiles f F r *
        contactResidual r (profileT F r) (profileY F r)
          (profileK f F r ^ 2 - 1) (profileEta f F r) :=
      mul_pos (mul_pos (pow_pos hr.1 _) hWeight) hContactPos
    have hsquare : b r ^ 2 = 0 := by
      have hProduct :
          (r ^ m * piconeWeightFromProfiles f F r *
            contactResidual r (profileT F r) (profileY F r)
              (profileK f F r ^ 2 - 1) (profileEta f F r)) *
              b r ^ 2 = 0 := by
        simpa only [Rem, profilePiconeRemainder, mul_assoc]
          using hRem0
      exact (mul_eq_zero.mp hProduct).resolve_left (ne_of_gt hcoef)
    nlinarith [hsquare]
  have hbContinuous : ContinuousOn b (Ioo (0 : ℝ) R) := by
    intro r hr
    exact (hb r hr).continuousAt.continuousWithinAt
  have hbEqOn := Measure.eqOn_open_of_ae_eq hbAEOpen
    isOpen_Ioo hbContinuous continuousOn_const
  intro r hr
  exact hbEqOn hr

end

end BrezisOP6
