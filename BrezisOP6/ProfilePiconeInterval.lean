import BrezisOP6.ProfilePiconeFull

/-!
# The finite-interval radial Picone identity from two profiles

The identity holds on every regular interval `[δ,R]` with `0<δ≤R`.  Both
boundary fluxes remain visible.  The lower bound at a vanishing outer trace
retains the inner flux; no limit as `δ→0` is asserted.
-/

namespace BrezisOP6

noncomputable section

/-- The density after removing the zero-mode pole. -/
def profilePiconeDensity (m : ℕ) (f F b db : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 2) * piconeWeightFromProfiles f F r * db r ^ 2 +
    r ^ (m + 1) * deriv (piconeWeightFromProfiles f F) r * b r ^ 2

/-- The nonnegative square in the profile Picone transform. -/
def profilePiconeSquare (m : ℕ) (f F b db : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 2) * piconeWeightFromProfiles f F r *
    piconeMultiplierFromProfiles f F r ^ 2 *
      (db r / piconeMultiplierFromProfiles f F r -
        b r * deriv (piconeMultiplierFromProfiles f F) r /
          piconeMultiplierFromProfiles f F r ^ 2) ^ 2

/-- The boundary flux, with the multiplier expressed through the profiles. -/
def profilePiconeBoundaryFlux (m : ℕ) (f F b : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialPiconeTheta m
    (piconeWeightFromProfiles f F)
    (piconeMultiplierFromProfiles f F)
    (profileY F) (profileK f F) (profileEta f F) r /
      piconeMultiplierFromProfiles f F r * b r ^ 2

/-- The remainder is exactly `r^(n-3) h S b²` for `n=m+3`. -/
def profilePiconeRemainder (m : ℕ) (f F b : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ m * piconeWeightFromProfiles f F r *
    contactResidual r (profileT F r) (profileY F r)
      (profileK f F r ^ 2 - 1) (profileEta f F r) * b r ^ 2

/-- The flux has an ordinary derivative wherever the original profiles
have the displayed second derivatives and the denominator `M` is positive. -/
theorem profilePiconeBoundaryFlux_differentiableAt
    (m : ℕ) (f F b : ℝ → ℝ)
    (r f₁ F₁ f₂ F₂ db : ℝ)
    (hr : 0 < r) (hFpos : 0 < F r)
    (hMpos : 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hb : HasDerivAt b db r) :
    DifferentiableAt ℝ (profilePiconeBoundaryFlux m f F b) r := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hMne : profileM f F r ≠ 0 := ne_of_gt hMpos
  have hhDiff : DifferentiableAt ℝ
      (piconeWeightFromProfiles f F) r := by
    unfold piconeWeightFromProfiles
    exact ((hf.differentiableAt.pow 2).sub
      (hF.differentiableAt.pow 2)).div
        ((hasDerivAt_pow 2 r).differentiableAt) (pow_ne_zero 2 hrne)
  have hkDiff : DifferentiableAt ℝ (profileK f F) r :=
    (profileK_hasDerivAt f F r f₁ F₁ hf hF hFne).differentiableAt
  have hMDiff : DifferentiableAt ℝ (profileM f F) r :=
    (hkDiff.pow 2).sub_const 1
  have hsne : Real.sqrt (profileM f F r) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hMpos)
  have hdenne : r * Real.sqrt (profileM f F r) ≠ 0 :=
    mul_ne_zero hrne hsne
  have hphiDiff : DifferentiableAt ℝ
      (piconeMultiplierFromProfiles f F) r := by
    unfold piconeMultiplierFromProfiles
    exact (hF.div
      ((hasDerivAt_id r).mul (hMDiff.hasDerivAt.sqrt hMne))
      hdenne).differentiableAt
  have hyDiff : DifferentiableAt ℝ (profileY F) r := by
    unfold profileY
    exact (((hasDerivAt_id r).mul hdF).div hF hFne).const_sub 1
      |>.differentiableAt
  have hetaDiff := profileEta_differentiableAt_from_profiles m f F r
    f₁ F₁ f₂ F₂ hr hFpos hMpos hfDiff hFDiff hf hF hdf hdF
  have hPdiff : DifferentiableAt ℝ
      (fun x => piconeMultiplierLogSlope (profileY F x)
        (profileK f F x) (profileEta f F x)) r := by
    simpa [piconeMultiplierLogSlope] using
      (hyDiff.add (hkDiff.mul hetaDiff)).neg
  have hThetaDiff : DifferentiableAt ℝ
      (radialPiconeTheta m
        (piconeWeightFromProfiles f F)
        (piconeMultiplierFromProfiles f F)
        (profileY F) (profileK f F) (profileEta f F)) r := by
    unfold radialPiconeTheta
    exact (((hasDerivAt_pow (m + 1) r).differentiableAt.mul hhDiff).mul
      hphiDiff).mul hPdiff
  unfold profilePiconeBoundaryFlux
  exact (hThetaDiff.div hphiDiff
    (ne_of_gt (piconeMultiplier_pos f F r hr hFpos hMpos))).mul
      (hb.differentiableAt.pow 2)

/-- Integrating the profile-level Picone identity on `[δ,R]` retains the
two explicit endpoint fluxes.  The regularity and integrability assumptions
are stated at finite radius; no singular endpoint limit enters the proof. -/
theorem profilePicone_interval
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hFpos : ∀ x ∈ Set.uIcc δ R, 0 < F x)
    (hMpos : ∀ x ∈ Set.uIcc δ R, 0 < profileM f F x)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ x ∈ Set.uIcc δ R,
      HasDerivAt (deriv f) (f₂ x) x)
    (hdF : ∀ x ∈ Set.uIcc δ R,
      HasDerivAt (deriv F) (F₂ x) x)
    (hode_f : ∀ x ∈ Set.uIcc δ R,
      radialODEAt ((m : ℝ) + 3) x (f x) (deriv f x) (f₂ x))
    (hode_F : ∀ x ∈ Set.uIcc δ R,
      radialODEAt ((m : ℝ) + 3) x (F x) (deriv F x) (F₂ x))
    (hb : ∀ x ∈ Set.uIcc δ R, HasDerivAt b (db x) x)
    (hsq_int : IntervalIntegrable (profilePiconeSquare m f F b db)
      MeasureTheory.volume δ R)
    (hflux_int : IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b))
      MeasureTheory.volume δ R)
    (hrem_int : IntervalIntegrable (profilePiconeRemainder m f F b)
      MeasureTheory.volume δ R) :
    (∫ x in δ..R, profilePiconeDensity m f F b db x) =
      (∫ x in δ..R, profilePiconeSquare m f F b db x) +
      (profilePiconeBoundaryFlux m f F b R -
        profilePiconeBoundaryFlux m f F b δ) +
      (∫ x in δ..R, profilePiconeRemainder m f F b x) := by
  have hflux_diff : ∀ x ∈ Set.uIcc δ R,
      DifferentiableAt ℝ (profilePiconeBoundaryFlux m f F b) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc δ R := by
      simpa [Set.uIcc_of_le hδR] using hx
    have hxpos : 0 < x := lt_of_lt_of_le hδ hxIcc.1
    exact profilePiconeBoundaryFlux_differentiableAt m f F b x
      (deriv f x) (deriv F x) (f₂ x) (F₂ x) (db x)
      hxpos (hFpos x hx) (hMpos x hx) hfDiff hFDiff
      (hfDiff x).hasDerivAt (hFDiff x).hasDerivAt
      (hdf x hx) (hdF x hx) (hb x hx)
  have hpoint : Set.EqOn
      (profilePiconeDensity m f F b db)
      (fun x => profilePiconeSquare m f F b db x +
        deriv (profilePiconeBoundaryFlux m f F b) x +
        profilePiconeRemainder m f F b x)
      (Set.uIcc δ R) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc δ R := by
      simpa [Set.uIcc_of_le hδR] using hx
    have hxpos : 0 < x := lt_of_lt_of_le hδ hxIcc.1
    have hraw := radial_picone_pointwise_from_profiles m f F b x
      (deriv f x) (deriv F x) (f₂ x) (F₂ x) (db x)
      hxpos (hFpos x hx) (hMpos x hx) hfDiff hFDiff
      (hfDiff x).hasDerivAt (hFDiff x).hasDerivAt
      (hdf x hx) (hdF x hx) (hode_f x hx) (hode_F x hx)
      (hb x hx)
    simpa only [profilePiconeDensity, profilePiconeSquare,
      profilePiconeBoundaryFlux, profilePiconeRemainder] using hraw
  calc
    (∫ x in δ..R, profilePiconeDensity m f F b db x) =
      ∫ x in δ..R, profilePiconeSquare m f F b db x +
        deriv (profilePiconeBoundaryFlux m f F b) x +
        profilePiconeRemainder m f F b x :=
      intervalIntegral.integral_congr hpoint
    _ = _ := by
      rw [intervalIntegral.integral_add (hsq_int.add hflux_int) hrem_int,
        intervalIntegral.integral_add hsq_int hflux_int,
        intervalIntegral.integral_deriv_eq_sub hflux_diff hflux_int]

/-- If `S≥0` on `[δ,R]` and `b(R)=0`, the zero-mode density dominates
the negative inner boundary flux.  The inner flux remains explicit. -/
theorem profilePicone_interval_lower_bound
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hFpos : ∀ x ∈ Set.uIcc δ R, 0 < F x)
    (hMpos : ∀ x ∈ Set.uIcc δ R, 0 < profileM f F x)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ x ∈ Set.uIcc δ R,
      HasDerivAt (deriv f) (f₂ x) x)
    (hdF : ∀ x ∈ Set.uIcc δ R,
      HasDerivAt (deriv F) (F₂ x) x)
    (hode_f : ∀ x ∈ Set.uIcc δ R,
      radialODEAt ((m : ℝ) + 3) x (f x) (deriv f x) (f₂ x))
    (hode_F : ∀ x ∈ Set.uIcc δ R,
      radialODEAt ((m : ℝ) + 3) x (F x) (deriv F x) (F₂ x))
    (hb : ∀ x ∈ Set.uIcc δ R, HasDerivAt b (db x) x)
    (hS : ∀ x ∈ Set.uIcc δ R,
      0 ≤ contactResidual x (profileT F x) (profileY F x)
        (profileK f F x ^ 2 - 1) (profileEta f F x))
    (hbR : b R = 0)
    (hsq_int : IntervalIntegrable (profilePiconeSquare m f F b db)
      MeasureTheory.volume δ R)
    (hflux_int : IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b))
      MeasureTheory.volume δ R)
    (hrem_int : IntervalIntegrable (profilePiconeRemainder m f F b)
      MeasureTheory.volume δ R) :
    -profilePiconeBoundaryFlux m f F b δ ≤
      ∫ x in δ..R, profilePiconeDensity m f F b db x := by
  have hsq_nonneg : 0 ≤
      ∫ x in δ..R, profilePiconeSquare m f F b db x := by
    apply intervalIntegral.integral_nonneg hδR
    intro x hx
    have hxU : x ∈ Set.uIcc δ R := by
      simpa [Set.uIcc_of_le hδR] using hx
    have hxpos : 0 < x := lt_of_lt_of_le hδ hx.1
    have hhpos := piconeWeight_pos f F x hxpos (hFpos x hxU)
      (hMpos x hxU)
    unfold profilePiconeSquare
    have hphipos := piconeMultiplier_pos f F x hxpos
      (hFpos x hxU) (hMpos x hxU)
    positivity
  have hrem_nonneg : 0 ≤
      ∫ x in δ..R, profilePiconeRemainder m f F b x := by
    apply intervalIntegral.integral_nonneg hδR
    intro x hx
    have hxU : x ∈ Set.uIcc δ R := by
      simpa [Set.uIcc_of_le hδR] using hx
    have hxpos : 0 < x := lt_of_lt_of_le hδ hx.1
    have hhpos := piconeWeight_pos f F x hxpos (hFpos x hxU)
      (hMpos x hxU)
    have hSpos := hS x hxU
    unfold profilePiconeRemainder
    positivity
  have houter : profilePiconeBoundaryFlux m f F b R = 0 := by
    simp [profilePiconeBoundaryFlux, hbR]
  have hident := profilePicone_interval m f F b db f₂ F₂ δ R
    hδ hδR hFpos hMpos hfDiff hFDiff hdf hdF hode_f hode_F hb
    hsq_int hflux_int hrem_int
  rw [houter] at hident
  linarith

end

end BrezisOP6
