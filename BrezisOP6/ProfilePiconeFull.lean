import BrezisOP6.PiconeSlopesFromProfiles
import BrezisOP6.EtaFlowFromProfiles
import BrezisOP6.PiconeFromFlow

/-!
# The pointwise radial Picone identity from two profile equations

The three flow equations and both logarithmic slopes are consequences of the
original radial equations.  This module inserts those consequences into the
general Picone identity.  The statement is local at a positive radius and
keeps the derivative of the boundary flux; no endpoint limit is taken here.
-/

namespace BrezisOP6

noncomputable section

/-- For `n=m+3`, the zero-mode radial density is a Picone square, the
derivative of its boundary flux, and the exact `r^m h S b²` remainder.
The hypotheses contain the two original profile equations, not the
derived `y`, `k`, or `η` flow equations. -/
theorem radial_picone_pointwise_from_profiles
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
    (hode_f : radialODEAt ((m : ℝ) + 3) r (f r) f₁ f₂)
    (hode_F : radialODEAt ((m : ℝ) + 3) r (F r) F₁ F₂)
    (hb : HasDerivAt b db r) :
    r ^ (m + 2) * piconeWeightFromProfiles f F r * db ^ 2 +
        r ^ (m + 1) * deriv (piconeWeightFromProfiles f F) r * b r ^ 2 =
      r ^ (m + 2) * piconeWeightFromProfiles f F r *
        piconeMultiplierFromProfiles f F r ^ 2 *
        (db / piconeMultiplierFromProfiles f F r -
          b r * deriv (piconeMultiplierFromProfiles f F) r /
            piconeMultiplierFromProfiles f F r ^ 2) ^ 2 +
      deriv (fun x => radialPiconeTheta m
        (piconeWeightFromProfiles f F)
        (piconeMultiplierFromProfiles f F)
        (profileY F) (profileK f F) (profileEta f F) x /
        piconeMultiplierFromProfiles f F x * b x ^ 2) r +
      r ^ m * piconeWeightFromProfiles f F r *
        contactResidual r (profileT F r) (profileY F r)
          (profileK f F r ^ 2 - 1) (profileEta f F r) * b r ^ 2 := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hMne : profileM f F r ≠ 0 := ne_of_gt hMpos
  have hphiPos := piconeMultiplier_pos f F r hr hFpos hMpos
  have hhDiff : DifferentiableAt ℝ
      (piconeWeightFromProfiles f F) r := by
    unfold piconeWeightFromProfiles
    exact ((hf.differentiableAt.pow 2).sub
      (hF.differentiableAt.pow 2)).div
        ((hasDerivAt_pow 2 r).differentiableAt) (pow_ne_zero 2 hrne)
  have hh : HasDerivAt (piconeWeightFromProfiles f F)
      (deriv (piconeWeightFromProfiles f F) r) r := hhDiff.hasDerivAt
  have hk := profileK_hasDerivAt f F r f₁ F₁ hf hF hFne
  have hkAt : HasDerivAt (profileK f F)
      (deriv (profileK f F) r) r := hk.differentiableAt.hasDerivAt
  have hMDiff : DifferentiableAt ℝ (profileM f F) r := by
    exact (hk.differentiableAt.pow 2).sub_const 1
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
  have hphi : HasDerivAt (piconeMultiplierFromProfiles f F)
      (deriv (piconeMultiplierFromProfiles f F) r) r :=
    hphiDiff.hasDerivAt
  have hyDiff : DifferentiableAt ℝ (profileY F) r := by
    unfold profileY
    exact (((hasDerivAt_id r).mul hdF).div hF hFne).const_sub 1
      |>.differentiableAt
  have hy : HasDerivAt (profileY F) (deriv (profileY F) r) r :=
    hyDiff.hasDerivAt
  have hetaDiff := profileEta_differentiableAt_from_profiles m f F r
    f₁ F₁ f₂ F₂ hr hFpos hMpos hfDiff hFDiff hf hF hdf hdF
  have heta : HasDerivAt (profileEta f F)
      (deriv (profileEta f F) r) r := hetaDiff.hasDerivAt
  have hhne : piconeWeightFromProfiles f F r ≠ 0 :=
    ne_of_gt (piconeWeight_pos f F r hr hFpos hMpos)
  have hphine : piconeMultiplierFromProfiles f F r ≠ 0 :=
    ne_of_gt hphiPos
  have hweight :
      r * deriv (piconeWeightFromProfiles f F) r =
        piconeWeightFromProfiles f F r *
          piconeWeightLogSlope (profileY F r)
            (profileK f F r) (profileEta f F r) := by
    have hslope := piconeWeight_logSlope_from_profiles f F r f₁ F₁
      hr hFpos hMpos hf hF
    rw [div_eq_iff hhne] at hslope
    simpa [mul_comm] using hslope
  have hmult :
      r * deriv (piconeMultiplierFromProfiles f F) r =
        piconeMultiplierFromProfiles f F r *
          piconeMultiplierLogSlope (profileY F r)
            (profileK f F r) (profileEta f F r) := by
    have hslope := piconeMultiplier_logSlope_from_profiles f F r f₁ F₁
      hr hFpos hMpos hf hF
    rw [div_eq_iff hphine] at hslope
    simpa [mul_comm] using hslope
  have hyFlow :
      r * deriv (profileY F) r =
        profileY F r ^ 2 - ((m : ℝ) + 3) * profileY F r +
          r ^ 2 - profileT F r ^ 2 :=
    profileY_flow ((m : ℝ) + 3) F r F₁ F₂ hFpos hF hdF hode_F
  have hkFlow :
      r * deriv (profileK f F) r =
        (profileK f F r ^ 2 - 1) * profileEta f F r := by
    change r * deriv (profileK f F) r =
      profileM f F r *
        (r * deriv (profileK f F) r / profileM f F r)
    field_simp [hMne]
  have hetaFlow :
      r * deriv (profileEta f F) r =
        profileK f F r * profileT F r ^ 2 -
          (((m : ℝ) + 3) - 2 * profileY F r) *
            profileEta f F r -
          2 * profileK f F r * profileEta f F r ^ 2 :=
    profileEta_flow_from_ODE m f F r f₁ F₁ f₂ F₂ hr hFpos hMpos
      hfDiff hFDiff hf hF hdf hdF hode_f hode_F
  exact radial_picone_pointwise_from_flow m
    (piconeWeightFromProfiles f F)
    (piconeMultiplierFromProfiles f F)
    (profileY F) (profileK f F) (profileEta f F) b
    r (profileT F r)
    (deriv (piconeWeightFromProfiles f F) r)
    (deriv (piconeMultiplierFromProfiles f F) r)
    (deriv (profileY F) r)
    (deriv (profileK f F) r)
    (deriv (profileEta f F) r) db
    hphiPos hh hphi hy hkAt heta hb hweight hmult hyFlow hkFlow hetaFlow

end

end BrezisOP6
