import BrezisOP6.ZeroModeAnnularCoercivity

/-!
# Annular Picone coercivity without global integrability of the parts

The Picone square and positive contact remainder need only be integrable
on punctured intervals.  Integrability of their sum separately at the
origin is not needed: take the exact interval identity at `ε>0`, discard
the nonnegative square, and then let `ε ↓ 0` using integrability of the
original density and the vanishing origin flux.
-/

namespace BrezisOP6

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- The full zero-mode quadratic form controls the contact remainder on
each annulus away from zero.  Only the original quadratic density is
assumed globally integrable. -/
theorem profilePicone_remainder_annular_le_full_density_sharp
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
  have hR : 0 < R := lt_of_lt_of_le hδ hδR
  have hDlim := annular_integral_left_tendsto D R hR hDint
  obtain ⟨B, hbRight⟩ := hblim
  have hFluxlim : Tendsto Flux (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    profilePiconeBoundaryFlux_tendsto_zero_of_right_limit
      m f F b R B hR hFpos hMpos hfactor hbRight
  have hRightLim : Tendsto
      (fun ε : ℝ => (∫ r in ε..R, D r) + Flux ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ r in (0 : ℝ)..R, D r)) := by
    simpa only [add_zero] using hDlim.add hFluxlim
  have hEv : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (∫ r in δ..R, Rem r) ≤
        (∫ r in ε..R, D r) + Flux ε := by
    filter_upwards [Ioc_mem_nhdsGT hδ] with ε hε
    have hεR : ε ≤ R := hε.2.trans hδR
    have hsubset : uIcc ε R ⊆ Ioc (0 : ℝ) R := by
      intro r hr
      have hrI : r ∈ Icc ε R := by
        simpa only [uIcc_of_le hεR] using hr
      exact ⟨lt_of_lt_of_le hε.1 hrI.1, hrI.2⟩
    have hsubsetOpen : uIoo ε R ⊆ Ioo (0 : ℝ) R := by
      intro r hr
      have hrI : r ∈ Ioo ε R := by
        simpa only [uIoo_of_le hεR] using hr
      exact ⟨lt_trans hε.1 hrI.1, hrI.2⟩
    have hident := profilePicone_interval_interior
      m f F b db f₂ F₂ ε R hε.1 hεR
      (fun r hr => hFpos r (hsubset hr))
      (fun r hr => hMpos r (hsubset hr))
      hfDiff hFDiff
      (fun r hr => hdf r (hsubsetOpen hr))
      (fun r hr => hdF r (hsubsetOpen hr))
      (fun r hr => hode_f r (hsubsetOpen hr))
      (fun r hr => hode_F r (hsubsetOpen hr))
      (fun r hr => hb r (hsubsetOpen hr))
      (hsq_int ε hε.1 hεR)
      (hflux_cont ε hε.1 hεR)
      (hflux_int ε hε.1 hεR)
      (hrem_int ε hε.1 hεR)
    have hOuter : Flux R = 0 := by
      simp [Flux, profilePiconeBoundaryFlux, hbR]
    change (∫ r in ε..R, D r) =
      (∫ r in ε..R, Sq r) + (Flux R - Flux ε) +
        (∫ r in ε..R, Rem r) at hident
    rw [hOuter] at hident
    have hSqNonneg : 0 ≤ ∫ r in ε..R, Sq r := by
      apply intervalIntegral.integral_nonneg hεR
      intro r hr
      have hr' : r ∈ Ioc (0 : ℝ) R :=
        ⟨lt_of_lt_of_le hε.1 hr.1, hr.2⟩
      have hWeight := piconeWeight_pos f F r hr'.1
        (hFpos r hr') (hMpos r hr')
      dsimp [Sq, profilePiconeSquare]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (pow_nonneg hr'.1.le _) hWeight.le)
          (sq_nonneg _))
        (sq_nonneg _)
    have hRemNonnegAE :
        0 ≤ᵐ[volume.restrict (Ioc ε R)] Rem := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hr' : r ∈ Ioc (0 : ℝ) R :=
        ⟨lt_trans hε.1 hr.1, hr.2⟩
      have hWeight := piconeWeight_pos f F r hr'.1
        (hFpos r hr') (hMpos r hr')
      have hContact := hSnonneg r hr'
      dsimp [Rem, profilePiconeRemainder,
        profileContactResidual, profileM, ratioM] at *
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg hr'.1.le _) hWeight.le)
          hContact) (sq_nonneg (b r))
    have hRemAnn : (∫ r in δ..R, Rem r) ≤
        ∫ r in ε..R, Rem r :=
      intervalIntegral.integral_mono_interval
        hε.2 hδR le_rfl hRemNonnegAE (hrem_int ε hε.1 hεR)
    dsimp [D, Sq, Rem, Flux] at hident hRemAnn ⊢
    linarith
  have hRightNeg : Tendsto
      (fun ε : ℝ => -((∫ r in ε..R, D r) + Flux ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(∫ r in (0 : ℝ)..R, D r))) := hRightLim.neg
  have hEvNeg : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      -((∫ r in ε..R, D r) + Flux ε) ≤
        -(∫ r in δ..R, Rem r) := by
    filter_upwards [hEv] with ε hε
    linarith
  have hlimit := le_of_tendsto hRightNeg hEvNeg
  dsimp [D, Rem] at hlimit ⊢
  linarith

/-- Quantitative zero-mode rigidity on a compact annulus, with no global
integrability assumption on the nonnegative Picone pieces. -/
theorem profilePicone_zero_mode_annular_l2_from_profiles_sharp
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
  have hδR : δ ≤ R := hδρ.trans hρR.le
  have hQ := profilePicone_remainder_annular_le_full_density_sharp
    m f F b db f₂ F₂ δ R hδ hδR hFpos hMpos
    hfDiff hFDiff hdf hdF hode_f hode_F hb hSnonneg hbR
    hDint hsq_int hflux_cont hflux_int hrem_int hfactor hblim
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
