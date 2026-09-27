import BrezisOP6.FlowFromProfiles
import BrezisOP6.PiconeResidual

/-!
# Picone logarithmic slopes from the original radial profiles

The algebraic Picone residual uses two logarithmic slopes.  This module
verifies that they are the slopes of the actual weight
`h=(f²-F²)/r²` and multiplier `φ=F/(r√M)`, with `k=f/F`,
`M=k²-1`, `y=1-rF'/F`, and `η=rk'/M`.
-/

namespace BrezisOP6

noncomputable section

def piconeWeightFromProfiles (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  (f r ^ 2 - F r ^ 2) / r ^ 2

def piconeMultiplierFromProfiles (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  F r / (r * Real.sqrt (profileM f F r))

theorem piconeWeight_eq_ratio
    (f F : ℝ → ℝ) (r : ℝ)
    (hFne : F r ≠ 0) :
    piconeWeightFromProfiles f F r =
      F r ^ 2 * profileM f F r / r ^ 2 := by
  unfold piconeWeightFromProfiles profileM ratioM profileK
  field_simp [hFne]

theorem piconeWeight_pos
    (f F : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r) (hF : 0 < F r)
    (hM : 0 < profileM f F r) :
    0 < piconeWeightFromProfiles f F r := by
  rw [piconeWeight_eq_ratio f F r (ne_of_gt hF)]
  exact div_pos (mul_pos (sq_pos_of_pos hF) hM) (sq_pos_of_pos hr)

/-- The actual radial contrast weight satisfies
`r h'/h = 2(kη-y)` wherever the three denominators are positive. -/
theorem piconeWeight_logSlope_from_profiles
    (f F : ℝ → ℝ) (r f₁ F₁ : ℝ)
    (hr : 0 < r) (hFpos : 0 < F r)
    (hMpos : 0 < profileM f F r)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r) :
    r * deriv (piconeWeightFromProfiles f F) r /
        piconeWeightFromProfiles f F r =
      piconeWeightLogSlope (profileY F r)
        (profileK f F r) (profileEta f F r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hMne : profileM f F r ≠ 0 := ne_of_gt hMpos
  have hhpos := piconeWeight_pos f F r hr hFpos hMpos
  have hhne : piconeWeightFromProfiles f F r ≠ 0 := ne_of_gt hhpos
  have hΔpos : 0 < f r ^ 2 - F r ^ 2 := by
    unfold piconeWeightFromProfiles at hhpos
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hr)).mp hhpos
  have hΔne : f r ^ 2 - F r ^ 2 ≠ 0 := ne_of_gt hΔpos
  have hMexpr : (f r / F r) ^ 2 - 1 ≠ 0 := by
    simpa [profileM, ratioM, profileK] using hMne
  have hnum : HasDerivAt (fun x => f x ^ 2 - F x ^ 2)
      (2 * f r * f₁ - 2 * F r * F₁) r := by
    convert (hf.fun_pow 2).sub (hF.fun_pow 2) using 1
    ring
  have hden : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    convert (hasDerivAt_pow 2 r) using 1
    norm_num
  have hh : HasDerivAt (piconeWeightFromProfiles f F)
      (((2 * f r * f₁ - 2 * F r * F₁) * r ^ 2
          - (f r ^ 2 - F r ^ 2) * (2 * r)) / (r ^ 2) ^ 2) r := by
    simpa [piconeWeightFromProfiles] using
      hnum.div hden (pow_ne_zero 2 hrne)
  have hk := profileK_hasDerivAt f F r f₁ F₁ hf hF hFne
  rw [hh.deriv]
  unfold piconeWeightFromProfiles piconeWeightLogSlope
    profileY profileEta
  rw [hF.deriv, hk.deriv]
  unfold profileM ratioM profileK
  field_simp [hrne, hFne, hMexpr, hΔne]
  ring

theorem piconeMultiplier_pos
    (f F : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r) (hF : 0 < F r)
    (hM : 0 < profileM f F r) :
    0 < piconeMultiplierFromProfiles f F r := by
  unfold piconeMultiplierFromProfiles
  exact div_pos hF (mul_pos hr (Real.sqrt_pos.2 hM))

/-- The actual Picone multiplier satisfies
`r φ'/φ = -(y+kη)` without invoking either profile's second-order ODE. -/
theorem piconeMultiplier_logSlope_from_profiles
    (f F : ℝ → ℝ) (r f₁ F₁ : ℝ)
    (hr : 0 < r) (hFpos : 0 < F r)
    (hMpos : 0 < profileM f F r)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r) :
    r * deriv (piconeMultiplierFromProfiles f F) r /
        piconeMultiplierFromProfiles f F r =
      piconeMultiplierLogSlope (profileY F r)
        (profileK f F r) (profileEta f F r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hMne : profileM f F r ≠ 0 := ne_of_gt hMpos
  have hspos : 0 < Real.sqrt (profileM f F r) := Real.sqrt_pos.2 hMpos
  have hsne : Real.sqrt (profileM f F r) ≠ 0 := ne_of_gt hspos
  have hs2 : (Real.sqrt (profileM f F r)) ^ 2 =
      profileM f F r := Real.sq_sqrt hMpos.le
  have hdenne : r * Real.sqrt (profileM f F r) ≠ 0 :=
    mul_ne_zero hrne hsne
  have hphine : piconeMultiplierFromProfiles f F r ≠ 0 :=
    ne_of_gt (piconeMultiplier_pos f F r hr hFpos hMpos)
  have hk := profileK_hasDerivAt f F r f₁ F₁ hf hF hFne
  let κ : ℝ := (f₁ * F r - f r * F₁) / F r ^ 2
  have hMderiv : HasDerivAt (profileM f F)
      (2 * profileK f F r * κ) r := by
    simpa only [profileM, ratioM, κ, Pi.pow_apply, Nat.reduceSub,
      pow_one, mul_assoc, mul_comm, mul_left_comm]
      using (hk.pow 2).sub_const 1
  have hsqrt : HasDerivAt
      (fun x => Real.sqrt (profileM f F x))
      ((2 * profileK f F r * κ) /
        (2 * Real.sqrt (profileM f F r))) r :=
    hMderiv.sqrt hMne
  have hden : HasDerivAt
      (fun x => x * Real.sqrt (profileM f F x))
      (Real.sqrt (profileM f F r) +
        r * ((2 * profileK f F r * κ) /
          (2 * Real.sqrt (profileM f F r)))) r := by
    simpa using (hasDerivAt_id r).mul hsqrt
  have hphi : HasDerivAt (piconeMultiplierFromProfiles f F)
      ((F₁ * (r * Real.sqrt (profileM f F r))
          - F r * (Real.sqrt (profileM f F r) +
            r * ((2 * profileK f F r * κ) /
              (2 * Real.sqrt (profileM f F r))))) /
        (r * Real.sqrt (profileM f F r)) ^ 2) r := by
    simpa [piconeMultiplierFromProfiles] using hF.div hden hdenne
  rw [hphi.deriv]
  unfold piconeMultiplierFromProfiles piconeMultiplierLogSlope
    profileY profileEta
  rw [hF.deriv, hk.deriv]
  dsimp [κ]
  field_simp [hrne, hFne, hMne, hsne, hdenne, hphine]
  linear_combination
    (r * profileK f F r * (F r * f₁ - F₁ * f r)) * hs2

end

end BrezisOP6
