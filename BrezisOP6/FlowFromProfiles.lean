import Mathlib

/-!
# Radial flow from the profile ODE

This module derives the first two radial-flow equations directly from the
Ginzburg--Landau profile equation.  The profile itself is an input function;
no existence, uniqueness, or asymptotic statement is assumed or proved here.
-/

namespace BrezisOP6

def profileT (F : ℝ → ℝ) (r : ℝ) : ℝ := r * F r

noncomputable def profileY (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  1 - r * deriv F r / F r

/-- The radial ODE multiplied by `r²`; at `r>0` it is equivalent to
`F''+(n-1)F'/r-(n-1)F/r²+(1-F²)F=0`. -/
def radialODEAt (n r F₀ F₁ F₂ : ℝ) : Prop :=
  r ^ 2 * F₂ + (n - 1) * r * F₁ - (n - 1) * F₀
    + r ^ 2 * (1 - F₀ ^ 2) * F₀ = 0

theorem radialODEAt_iff_divided
    (n r F₀ F₁ F₂ : ℝ) (hr : 0 < r) :
    radialODEAt n r F₀ F₁ F₂ ↔
      F₂ + (n - 1) / r * F₁ - (n - 1) / r ^ 2 * F₀
        + (1 - F₀ ^ 2) * F₀ = 0 := by
  have hrne : r ≠ 0 := ne_of_gt hr
  constructor
  · intro h
    unfold radialODEAt at h
    field_simp [hrne]
    nlinarith [h]
  · intro h
    field_simp [hrne] at h
    unfold radialODEAt
    nlinarith [h]

/-- The first flow equation `r t' = t(2-y)` follows only from the
definitions and the first derivative of `F`. -/
theorem profileT_flow
    (F : ℝ → ℝ) (r F₁ : ℝ)
    (hFpos : 0 < F r)
    (hF : HasDerivAt F F₁ r) :
    r * deriv (profileT F) r =
      profileT F r * (2 - profileY F r) := by
  have hT : HasDerivAt (profileT F) (F r + r * F₁) r := by
    simpa [profileT] using (hasDerivAt_id r).mul hF
  rw [hT.deriv]
  unfold profileT profileY
  rw [hF.deriv]
  field_simp [ne_of_gt hFpos]
  ring

/-- The second flow equation `r y' = y² - n y + r² - t²`,
with the radial ODE as its only differential input. -/
theorem profileY_flow
    (n : ℝ) (F : ℝ → ℝ) (r F₁ F₂ : ℝ)
    (hFpos : 0 < F r)
    (hF : HasDerivAt F F₁ r)
    (hF' : HasDerivAt (deriv F) F₂ r)
    (hode : radialODEAt n r (F r) F₁ F₂) :
    r * deriv (profileY F) r =
      profileY F r ^ 2 - n * profileY F r
        + r ^ 2 - profileT F r ^ 2 := by
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hprod : HasDerivAt (fun x => x * deriv F x)
      (deriv F r + r * F₂) r := by
    simpa using (hasDerivAt_id r).mul hF'
  have hquot : HasDerivAt (fun x => x * deriv F x / F x)
      (((deriv F r + r * F₂) * F r - (r * deriv F r) * F₁)
        / F r ^ 2) r := by
    simpa using hprod.div hF hFne
  have hY : HasDerivAt (profileY F)
      (-(((deriv F r + r * F₂) * F r - (r * deriv F r) * F₁)
        / F r ^ 2)) r := by
    simpa [profileY] using hquot.const_sub 1
  rw [hY.deriv]
  unfold profileY profileT radialODEAt at *
  rw [hF.deriv]
  field_simp [hFne]
  nlinarith [hode]

def ratioM (k : ℝ → ℝ) (r : ℝ) : ℝ := k r ^ 2 - 1

/-- With `M=k²-1` and `eta=r k'/M`, the quotient flow obeys
`r M'=2k M eta` wherever `M≠0`. -/
theorem ratioM_flow
    (k eta : ℝ → ℝ) (r dk : ℝ)
    (hk : HasDerivAt k dk r)
    (hMne : ratioM k r ≠ 0)
    (heta : eta r = r * dk / ratioM k r) :
    r * deriv (ratioM k) r =
      2 * k r * ratioM k r * eta r := by
  have hderiv : HasDerivAt (ratioM k) (2 * k r * dk) r := by
    simpa only [ratioM, Pi.pow_apply, Nat.reduceSub, pow_one,
      mul_assoc, mul_comm, mul_left_comm]
      using (hk.pow 2).sub_const 1
  rw [hderiv.deriv, heta]
  field_simp [hMne]

noncomputable def profileK (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  f r / F r

noncomputable def profileM (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  ratioM (profileK f F) r

noncomputable def profileEta (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv (profileK f F) r / profileM f F r

theorem profileK_hasDerivAt
    (f F : ℝ → ℝ) (r f₁ F₁ : ℝ)
    (hf : HasDerivAt f f₁ r) (hF : HasDerivAt F F₁ r)
    (hFne : F r ≠ 0) :
    HasDerivAt (profileK f F)
      ((f₁ * F r - f r * F₁) / F r ^ 2) r := by
  simpa [profileK] using hf.div hF hFne

/-- The `M`-flow expressed in terms of the original pair of profiles.
Only first derivatives and nonvanishing denominators are used. -/
theorem profileM_flow
    (f F : ℝ → ℝ) (r f₁ F₁ : ℝ)
    (hf : HasDerivAt f f₁ r) (hF : HasDerivAt F F₁ r)
    (hFne : F r ≠ 0) (hMne : profileM f F r ≠ 0) :
    r * deriv (profileM f F) r =
      2 * profileK f F r * profileM f F r * profileEta f F r := by
  have hk := profileK_hasDerivAt f F r f₁ F₁ hf hF hFne
  have heta : profileEta f F r =
      r * ((f₁ * F r - f r * F₁) / F r ^ 2)
        / ratioM (profileK f F) r := by
    simp [profileEta, profileM, hk.deriv]
  simpa [profileM] using
    (ratioM_flow (profileK f F) (profileEta f F) r
      ((f₁ * F r - f r * F₁) / F r ^ 2) hk hMne heta)

end BrezisOP6
