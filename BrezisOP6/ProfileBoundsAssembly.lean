import BrezisOP6.ProfileContactFromODE
import BrezisOP6.ProfileBarrierFromODE
import BrezisOP6.EtaGlobal
import BrezisOP6.RatioOrdering
import BrezisOP6.InitialRatioOrdering
import BrezisOP6.SlopeFluxGlobal

/-!
# Assembly of the contact-domain bounds from profile inequalities

The contact polynomial uses `X=χ`, a normalized logarithmic ratio growth.
Here `χ=r k'/(k y_F)` is tied to the original pair `f,F` by the elementary
identity `r k'/k = y_F-y_f`.  Consequently `0<y_f<y_F` gives `0<χ<1`.
The other contact-domain inequalities are supplied by the profile barrier,
the normalized-growth barrier, and strict ratio ordering.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- The normalized logarithmic ratio growth used in the contact domain. -/
def profileChi (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv (profileK f F) r /
    (profileK f F r * profileY F r)

/-- The exact quotient-slope identity `r k'=k(y_F-y_f)`. -/
theorem profileK_slope_difference
    (f F : ℝ → ℝ) (r f₁ F₁ : ℝ)
    (hfpos : 0 < f r) (hFpos : 0 < F r)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r) :
    r * deriv (profileK f F) r =
      profileK f F r * (profileY F r - profileY f r) := by
  have hk := profileK_hasDerivAt f F r f₁ F₁ hf hF
    (ne_of_gt hFpos)
  rw [hk.deriv]
  unfold profileK profileY
  rw [hf.deriv, hF.deriv]
  field_simp [ne_of_gt hfpos, ne_of_gt hFpos]
  ring

/-- The contact variable is the relative separation of the two
logarithmic slopes: `χ=1-y_f/y_F`. -/
theorem profileChi_eq_slope_ratio
    (f F : ℝ → ℝ) (r f₁ F₁ : ℝ)
    (hfpos : 0 < f r) (hFpos : 0 < F r)
    (hkpos : 0 < profileK f F r)
    (hyFne : profileY F r ≠ 0)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r) :
    profileChi f F r = 1 - profileY f r / profileY F r := by
  rw [profileChi, profileK_slope_difference f F r f₁ F₁
    hfpos hFpos hf hF]
  field_simp [ne_of_gt hkpos, hyFne]

/-- All eleven pointwise inequalities and identities required by the
contact theorem, with `q=F²` and `X=χ`.  The four analytic inputs are
strict ratio ordering, the two basic slope bounds, the profile barrier,
and the normalized-growth barrier. -/
theorem contact_bounds_from_profile_inequalities
    (f F : ℝ → ℝ) (r f₁ F₁ : ℝ)
    (hr : 0 < r) (hFpos : 0 < F r)
    (hkgt : 1 < profileK f F r)
    (hkderiv : 0 < deriv (profileK f F) r)
    (hyfpos : 0 < profileY f r)
    (hyFlt : profileY F r < 1)
    (hbarrier : profileY F r ≤ F r ^ 2)
    (hetaSmall : profileEta f F r < r / Real.sqrt 2)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r) :
    ∃ X q : ℝ,
      0 < profileM f F r ∧
      0 < profileY F r ∧ profileY F r < 1 ∧
      0 < profileK f F r ∧ 0 < profileEta f F r ∧
      profileEta f F r ^ 2 < r ^ 2 / 2 ∧
      0 < X ∧ X < 1 ∧
      profileM f F r * profileEta f F r =
        profileK f F r * X * profileY F r ∧
      profileY F r ≤ q ∧ profileT F r ^ 2 = r ^ 2 * q := by
  have hkpos : 0 < profileK f F r := by linarith
  have hfpos : 0 < f r := by
    have hdiv := hkgt
    unfold profileK at hdiv
    have hff : F r < f r := by
      have h := (lt_div_iff₀ hFpos).mp hdiv
      simpa using h
    linarith
  have hMpos : 0 < profileM f F r := by
    unfold profileM ratioM
    nlinarith
  have hslope := profileK_slope_difference f F r f₁ F₁
    hfpos hFpos hf hF
  have hyDiff : 0 < profileY F r - profileY f r := by
    have hprod : 0 < r * deriv (profileK f F) r :=
      mul_pos hr hkderiv
    rw [hslope] at hprod
    by_contra hnot
    have hle : profileY F r - profileY f r ≤ 0 :=
      le_of_not_gt hnot
    have hprodle := mul_nonpos_of_nonneg_of_nonpos hkpos.le hle
    linarith
  have hyFpos : 0 < profileY F r := by linarith
  have hXeq := profileChi_eq_slope_ratio f F r f₁ F₁
    hfpos hFpos hkpos (ne_of_gt hyFpos) hf hF
  have hXpos : 0 < profileChi f F r := by
    rw [hXeq]
    have hquot : profileY f r / profileY F r < 1 :=
      (div_lt_one hyFpos).2 (by linarith)
    linarith
  have hXlt : profileChi f F r < 1 := by
    rw [hXeq]
    have hquot : 0 < profileY f r / profileY F r :=
      div_pos hyfpos hyFpos
    linarith
  have hetaPos : 0 < profileEta f F r := by
    unfold profileEta
    exact div_pos (mul_pos hr hkderiv) hMpos
  have hrootPos : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hrootSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hUpperSq : (r / Real.sqrt 2) ^ 2 = r ^ 2 / 2 := by
    field_simp [ne_of_gt hrootPos]
    nlinarith [hrootSq]
  have hetaSqSmall : profileEta f F r ^ 2 < r ^ 2 / 2 := by
    have hUpperPos : 0 < r / Real.sqrt 2 := div_pos hr hrootPos
    have hsq : profileEta f F r ^ 2 < (r / Real.sqrt 2) ^ 2 := by
      have hprod : 0 < (r / Real.sqrt 2 - profileEta f F r) *
          (r / Real.sqrt 2 + profileEta f F r) := by
        apply mul_pos
        · linarith
        · linarith
      nlinarith
    rwa [hUpperSq] at hsq
  have hchi : profileM f F r * profileEta f F r =
      profileK f F r * profileChi f F r * profileY F r := by
    calc
      profileM f F r * profileEta f F r =
          r * deriv (profileK f F) r := by
        unfold profileEta
        field_simp [ne_of_gt hMpos]
      _ = profileK f F r * (profileY F r - profileY f r) := hslope
      _ = profileK f F r * profileChi f F r * profileY F r := by
        rw [hXeq]
        field_simp [ne_of_gt hyFpos]
  refine ⟨profileChi f F r, F r ^ 2,
    hMpos, hyFpos, hyFlt, hkpos, hetaPos, hetaSqSmall,
    hXpos, hXlt, hchi, hbarrier, ?_⟩
  unfold profileT
  ring

/-- The multiplied radial equation in dimension `n=m+3` has the divided
form used by both the slope-flux and ratio-flux comparison theorems. -/
theorem radialODEAt_divided_for_profile_flux
    (m : ℕ) (p : ℝ → ℝ) (r p₂ : ℝ)
    (hr : 0 < r)
    (hode : radialODEAt ((m : ℝ) + 3)
      r (p r) (deriv p r) p₂) :
    p₂ + (((m + 1 : ℕ) : ℝ) + 1) / r * deriv p r -
      (((m + 1 : ℕ) : ℝ) + 1) / r ^ 2 * p r +
      (1 - p r ^ 2) * p r = 0 := by
  convert (radialODEAt_iff_divided ((m : ℝ) + 3) r
    (p r) (deriv p r) p₂ hr).mp hode using 1
  push_cast
  ring

/-- Contact positivity for a ball profile using only bounds on `(0,R]`.
The pointwise contact domain is assembled from comparison, slopes, and the
two barriers; all profile ODE assumptions are local to the ball. -/
theorem profileContact_positive_on_ball_from_assembled_bounds
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hforder : ∀ r ∈ Set.Ioc 0 R, F r < f r)
    (hkderiv : ∀ r ∈ Set.Ioc 0 R,
      0 < deriv (profileK f F) r)
    (hyfpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileY f r)
    (hyFlt : ∀ r ∈ Set.Ioc 0 R, profileY F r < 1)
    (hbarrier : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ F r ^ 2 - profileY F r)
    (hetaSmall : ∀ r ∈ Set.Ioc 0 R,
      profileEta f F r < r / Real.sqrt 2)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3) r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r) (F₂ r))
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r) :
    ∀ r ∈ Set.Ioc 0 R, 0 < profileContactResidual f F r := by
  have hkgt : ∀ r ∈ Set.Ioc 0 R,
      1 < profileK f F r := by
    intro r hr
    unfold profileK
    exact (lt_div_iff₀ (hFpos r hr)).2 (by simpa using hforder r hr)
  have hMpos : ∀ r ∈ Set.Ioc 0 R,
      0 < profileM f F r := by
    intro r hr
    have hk := hkgt r hr
    unfold profileM ratioM
    nlinarith
  have haux : ∀ r ∈ Set.Ioc 0 R, ∃ X : ℝ,
      0 < profileY F r ∧ profileY F r < 1 ∧
      0 < profileK f F r ∧ 0 < profileEta f F r ∧
      profileEta f F r ^ 2 < r ^ 2 / 2 ∧
      0 < X ∧ X < 1 ∧
      profileM f F r * profileEta f F r =
        profileK f F r * X * profileY F r ∧
      profileY F r ≤ F r ^ 2 := by
    intro r hr
    obtain ⟨X, q, _, hy0, hy1, hk0, heta0, hetaSq,
      hX0, hX1, hchi, hq, htrel⟩ :=
      contact_bounds_from_profile_inequalities f F r
        (deriv f r) (deriv F r) hr.1 (hFpos r hr)
        (hkgt r hr) (hkderiv r hr) (hyfpos r hr)
        (hyFlt r hr) (by linarith [hbarrier r hr])
        (hetaSmall r hr) (hfDiff r).hasDerivAt
        (hFDiff r).hasDerivAt
    have hqeq : q = F r ^ 2 := by
      have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr.1)
      have hfactor : r ^ 2 * (F r ^ 2 - q) = 0 := by
        unfold profileT at htrel
        nlinarith [htrel]
      have hdiff : F r ^ 2 - q = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hr2
      linarith
    rw [hqeq] at hq
    exact ⟨X, hy0, hy1, hk0, heta0, hetaSq,
      hX0, hX1, hchi, hq⟩
  exact profileContact_positive_on_ball_interval m f F f₂ F₂ R
    hFpos hMpos hfDiff hFDiff hdf hdF hode_f hode_F haux hnear

/-- The slope-flux theorem yields `y_f>0` all the way to the ball
boundary when `f<1` holds on the **open** interval `(0,R)`; the admissible
boundary value `f(R)=1` is retained. -/
theorem profileY_pos_on_ball_from_flux
    (m : ℕ) (f f₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hfDiff : Differentiable ℝ f)
    (hfluxcont : ContinuousOn (slopeFlux (m + 2) f) (Set.Icc 0 R))
    (hfpos : ∀ r ∈ Set.Ioc 0 R, 0 < f r)
    (hflt : ∀ r ∈ Set.Ioo 0 R, f r < 1)
    (hdf : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioo 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r)) :
    ∀ r ∈ Set.Ioc 0 R, 0 < profileY f r := by
  have hodeDiv : ∀ r ∈ Set.Ioo 0 R,
      ∃ u : ℝ, HasDerivAt (deriv f) u r ∧
        u + (((m + 1 : ℕ) : ℝ) + 1) / r * deriv f r -
          (((m + 1 : ℕ) : ℝ) + 1) / r ^ 2 * f r +
          (1 - f r ^ 2) * f r = 0 := by
    intro r hr
    exact ⟨f₂ r, hdf r hr,
      radialODEAt_divided_for_profile_flux m f r (f₂ r) hr.1
        (hode_f r hr)⟩
  have hSlope := profile_logSlope_lt_one (m + 1) f R hR hfDiff
    (by simpa only [show (m + 1) + 1 = m + 2 by omega] using
      hfluxcont)
    hfpos hflt hodeDiv
  intro r hr
  have hs := hSlope r hr
  unfold profileY
  linarith

/-- The finite-ball weighted-ratio theorem gives both comparison outputs,
including the endpoint, from a regular-origin extension `k₀` with
`k₀(0)>1`.  The latter can be obtained from terminal ordering via
`InitialRatioOrdering` once regular-origin uniqueness is supplied. -/
theorem profile_ratio_ordering_on_ball_from_flux
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hkcont : ContinuousOn k₀ (Set.Icc 0 R))
    (hfluxcont : ContinuousOn (ratioFlux (m + 2) f F)
      (Set.Icc 0 R))
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hk0 : 1 < k₀ 0)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioo 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioo 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r)) :
    (∀ r ∈ Set.Ioc 0 R, F r < f r) ∧
    (∀ r ∈ Set.Ioc 0 R,
      0 < deriv (profileK f F) r) := by
  have hodeDivf : ∀ r ∈ Set.Ioo 0 R,
      ∃ u : ℝ, HasDerivAt (deriv f) u r ∧
        u + (((m + 1 : ℕ) : ℝ) + 1) / r * deriv f r -
          (((m + 1 : ℕ) : ℝ) + 1) / r ^ 2 * f r +
          (1 - f r ^ 2) * f r = 0 := by
    intro r hr
    exact ⟨f₂ r, hdf r hr,
      radialODEAt_divided_for_profile_flux m f r (f₂ r) hr.1
        (hode_f r hr)⟩
  have hodeDivF : ∀ r ∈ Set.Ioo 0 R,
      ∃ u : ℝ, HasDerivAt (deriv F) u r ∧
        u + (((m + 1 : ℕ) : ℝ) + 1) / r * deriv F r -
          (((m + 1 : ℕ) : ℝ) + 1) / r ^ 2 * F r +
          (1 - F r ^ 2) * F r = 0 := by
    intro r hr
    exact ⟨F₂ r, hdF r hr,
      radialODEAt_divided_for_profile_flux m F r (F₂ r) hr.1
        (hode_F r hr)⟩
  have hpair := ratio_ordering_profiles (m + 1)
    (f := f) (F := F) (k := k₀) (R := R)
    hR
    (by intro r _; exact hfDiff r)
    (by intro r _; exact hFDiff r)
    hkcont
    (by simpa only [show (m + 1) + 1 = m + 2 by omega] using
      hfluxcont)
    hFpos
    (by intro r hr; simpa only [profileK] using hkevent r hr)
    hk0 hodeDivf hodeDivF
  constructor
  · exact hpair.1
  · intro r hr
    simpa only [profileK] using hpair.2 r hr

/-- A larger terminal value `f(R)>F(R)` forces the regular-origin ratio
above one, provided the equal-initial-ratio solution is unique.  The
initial comparison is obtained by the verified `InitialRatioOrdering`
first-contact theorem, without assuming `k₀(0)>1`. -/
theorem profile_initial_ratio_gt_one_from_terminal
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hkcont : ContinuousOn k₀ (Set.Icc 0 R))
    (hfluxcont : ContinuousOn (ratioFlux (m + 2) f F)
      (Set.Icc 0 R))
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hunique_origin : k₀ 0 = 1 →
      ∀ r ∈ Set.Ioc 0 R, k₀ r = 1)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioo 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioo 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r)) :
    1 < k₀ 0 := by
  let A : ℝ → ℝ := fun r => r ^ (m + 2) * F r ^ 2
  let B : ℝ → ℝ := fun r => r ^ (m + 2) * F r ^ 4
  let q : ℝ → ℝ := ratioFlux (m + 2) f F
  have hkpoint : ∀ r ∈ Set.Ioc 0 R, k₀ r = profileK f F r := by
    intro r hr
    exact (hkevent r hr).eq_of_nhds
  have hkdiff : ∀ r ∈ Set.Ioc 0 R,
      DifferentiableAt ℝ k₀ r := by
    intro r hr
    have hdiv : DifferentiableAt ℝ (profileK f F) r :=
      (hfDiff r).div (hFDiff r) (ne_of_gt (hFpos r hr))
    exact hdiv.congr_of_eventuallyEq (hkevent r hr)
  have hq0 : q 0 = 0 := by simp [q, ratioFlux]
  have hApos : ∀ r ∈ Set.Ioc 0 R, 0 < A r := by
    intro r hr
    exact mul_pos (pow_pos hr.1 _) (sq_pos_of_pos (hFpos r hr))
  have hBpos : ∀ r ∈ Set.Ioo 0 R, 0 < B r := by
    intro r hr
    exact mul_pos (pow_pos hr.1 _)
      (pow_pos (hFpos r ⟨hr.1, hr.2.le⟩) _)
  have hrelation : ∀ r ∈ Set.Ioc 0 R,
      q r = A r * deriv k₀ r := by
    intro r hr
    have hFlux := ratioFlux_eq_ratio (m + 2)
      (hfDiff r) (hFDiff r) (ne_of_gt (hFpos r hr))
    have hderiv : deriv k₀ r =
        deriv (fun t => f t / F t) r := by
      simpa only [profileK] using (hkevent r hr).deriv_eq
    simpa only [q, A, hderiv] using hFlux
  have hflux : ∀ r ∈ Set.Ioo 0 R,
      deriv q r = B r * k₀ r * (k₀ r ^ 2 - 1) := by
    intro r hr
    have hrI : r ∈ Set.Ioc 0 R := ⟨hr.1, hr.2.le⟩
    have hODEf := radialODEAt_divided_for_profile_flux m f r (f₂ r)
      hr.1 (hode_f r hr)
    have hODEF := radialODEAt_divided_for_profile_flux m F r (F₂ r)
      hr.1 (hode_F r hr)
    have hFlux := deriv_ratioFlux (m + 1) (ne_of_gt hr.1)
      (hfDiff r).hasDerivAt (hFDiff r).hasDerivAt
      (hdf r hr) (hdF r hr) hODEf hODEF
    change deriv (ratioFlux (m + 2) f F) r =
      r ^ (m + 2) * F r ^ 4 * k₀ r * (k₀ r ^ 2 - 1)
    rw [show m + 2 = (m + 1) + 1 by omega] at *
    rw [hFlux, hkpoint r hrI]
    unfold profileK
    field_simp [ne_of_gt (hFpos r hrI)]
  have hkR : 1 < k₀ R := by
    rw [hkpoint R ⟨hR, le_rfl⟩]
    unfold profileK
    exact (lt_div_iff₀ (hFpos R ⟨hR, le_rfl⟩)).2
      (by simpa using hterminal)
  exact initial_ratio_gt_one_of_terminal hR hkcont hfluxcont
    hkdiff hkpos hq0 hApos hBpos hrelation hflux hkR hunique_origin

/-- A ball-profile contact theorem with `y_f>0` supplied by the verified
slope-flux argument.  It allows the regular Dirichlet value `f(R)=1`. -/
theorem profileContact_positive_on_ball_from_flux_bounds
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hforder : ∀ r ∈ Set.Ioc 0 R, F r < f r)
    (hkderiv : ∀ r ∈ Set.Ioc 0 R,
      0 < deriv (profileK f F) r)
    (hfpos : ∀ r ∈ Set.Ioc 0 R, 0 < f r)
    (hflt : ∀ r ∈ Set.Ioo 0 R, f r < 1)
    (hfluxcont : ContinuousOn (slopeFlux (m + 2) f)
      (Set.Icc 0 R))
    (hyFlt : ∀ r ∈ Set.Ioc 0 R, profileY F r < 1)
    (hbarrier : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ F r ^ 2 - profileY F r)
    (hetaSmall : ∀ r ∈ Set.Ioc 0 R,
      profileEta f F r < r / Real.sqrt 2)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r) :
    ∀ r ∈ Set.Ioc 0 R, 0 < profileContactResidual f F r := by
  have hyfpos := profileY_pos_on_ball_from_flux m f f₂ R hR
    hfDiff hfluxcont hfpos hflt
    (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
  exact profileContact_positive_on_ball_from_assembled_bounds
    m f F f₂ F₂ R hFpos hforder hkderiv hyfpos
    hyFlt hbarrier hetaSmall hfDiff hFDiff hdf hdF
    hode_f hode_F hnear

/-- Finite-ball contact positivity with both strict ratio ordering and
`y_f>0` obtained from their verified flux theorems.  The remaining
barrier conclusions `F²≥y_F` and `η<r/√2` are explicit inputs supplied
by the dedicated barrier modules below. -/
theorem profileContact_positive_on_ball_from_ratio_and_slope_flux
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hfpos : ∀ r ∈ Set.Ioc 0 R, 0 < f r)
    (hflt : ∀ r ∈ Set.Ioo 0 R, f r < 1)
    (hkcont : ContinuousOn k₀ (Set.Icc 0 R))
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hk0 : 1 < k₀ 0)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Set.Icc 0 R))
    (hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Set.Icc 0 R))
    (hyFlt : ∀ r ∈ Set.Ioc 0 R, profileY F r < 1)
    (hbarrier : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ F r ^ 2 - profileY F r)
    (hetaSmall : ∀ r ∈ Set.Ioc 0 R,
      profileEta f F r < r / Real.sqrt 2)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r) :
    ∀ r ∈ Set.Ioc 0 R, 0 < profileContactResidual f F r := by
  obtain ⟨hforder, hkderiv⟩ :=
    profile_ratio_ordering_on_ball_from_flux
      m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont hFpos
      hkevent hk0 hfDiff hFDiff
      (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
      (by intro r hr; exact hdF r ⟨hr.1, hr.2.le⟩)
      (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
      (by intro r hr; exact hode_F r ⟨hr.1, hr.2.le⟩)
  exact profileContact_positive_on_ball_from_flux_bounds
    m f F f₂ F₂ R hR hFpos hforder hkderiv hfpos hflt
    hSlopeFluxCont hyFlt hbarrier hetaSmall hfDiff hFDiff
    hdf hdF hode_f hode_F hnear

/-- The ball contact theorem starting from terminal comparison instead of
an assumed initial ratio.  The only extra origin condition is uniqueness
for the equal-initial-ratio regular solution. -/
theorem profileContact_positive_on_ball_from_terminal_flux
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hfpos : ∀ r ∈ Set.Ioc 0 R, 0 < f r)
    (hflt : ∀ r ∈ Set.Ioo 0 R, f r < 1)
    (hkcont : ContinuousOn k₀ (Set.Icc 0 R))
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hunique_origin : k₀ 0 = 1 →
      ∀ r ∈ Set.Ioc 0 R, k₀ r = 1)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Set.Icc 0 R))
    (hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Set.Icc 0 R))
    (hyFlt : ∀ r ∈ Set.Ioc 0 R, profileY F r < 1)
    (hbarrier : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ F r ^ 2 - profileY F r)
    (hetaSmall : ∀ r ∈ Set.Ioc 0 R,
      profileEta f F r < r / Real.sqrt 2)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r) :
    ∀ r ∈ Set.Ioc 0 R, 0 < profileContactResidual f F r := by
  have hk0 := profile_initial_ratio_gt_one_from_terminal
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
    hFpos hkevent hkpos hterminal hunique_origin hfDiff hFDiff
    (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hdF r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_F r ⟨hr.1, hr.2.le⟩)
  exact profileContact_positive_on_ball_from_ratio_and_slope_flux
    m f F k₀ f₂ F₂ R hR hFpos hfpos hflt hkcont hkevent
    hk0 hRatioFluxCont hSlopeFluxCont hyFlt hbarrier hetaSmall
    hfDiff hFDiff hdf hdF hode_f hode_F hnear

/-- The verified single-profile slope-flux theorem yields `y_p>0` on
the entire positive axis.  Continuity of the regular-origin flux remains
an explicit origin input. -/
theorem profileY_pos_from_slope_flux
    (m : ℕ) (p p₂ : ℝ → ℝ)
    (hpDiff : Differentiable ℝ p)
    (hfluxcont : ∀ R, 0 < R →
      ContinuousOn (slopeFlux (m + 2) p) (Set.Icc 0 R))
    (hppos : ∀ r, 0 < r → 0 < p r)
    (hplt : ∀ r, 0 < r → p r < 1)
    (hdp : ∀ r, 0 < r → HasDerivAt (deriv p) (p₂ r) r)
    (hode : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (p r) (deriv p r) (p₂ r)) :
    ∀ R, 0 < R → 0 < profileY p R := by
  intro R hR
  have hodeDiv : ∀ r ∈ Set.Ioo 0 R,
      ∃ p₂' : ℝ, HasDerivAt (deriv p) p₂' r ∧
        p₂' + (((m + 1 : ℕ) : ℝ) + 1) / r * deriv p r -
          (((m + 1 : ℕ) : ℝ) + 1) / r ^ 2 * p r +
          (1 - p r ^ 2) * p r = 0 := by
    intro r hr
    exact ⟨p₂ r, hdp r hr.1,
      radialODEAt_divided_for_profile_flux m p r (p₂ r) hr.1
        (hode r hr.1)⟩
  have hSlope := profile_logSlope_lt_one (m + 1) p R hR hpDiff
    (by simpa only [show (m + 1) + 1 = m + 2 by omega] using
      hfluxcont R hR)
    (by intro r hr; exact hppos r hr.1)
    (by intro r hr; exact hplt r hr.1)
    hodeDiv R ⟨hR, le_rfl⟩
  unfold profileY
  linarith

/-- The verified weighted ratio comparison supplies `F<f` and `k'>0`
on the whole positive axis by applying its finite-interval theorem at each
endpoint.  The regular-origin quotient extension and its initial value are
explicit, as are continuity of the weighted Wronskian flux and the ODE. -/
theorem profile_ratio_ordering_from_flux
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ)
    (hkcont : Continuous k₀)
    (hfluxcont : ∀ R, 0 < R →
      ContinuousOn (ratioFlux (m + 2) f F) (Set.Icc 0 R))
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hkevent : ∀ r, 0 < r →
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hk0 : 1 < k₀ 0)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r, 0 < r → HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r, 0 < r → HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (F r) (deriv F r) (F₂ r)) :
    (∀ r, 0 < r → F r < f r) ∧
    (∀ r, 0 < r → 0 < deriv (profileK f F) r) := by
  have hinterval (R : ℝ) (hR : 0 < R) :
      (∀ r ∈ Set.Ioc 0 R, F r < f r) ∧
      (∀ r ∈ Set.Ioc 0 R, 0 < deriv (profileK f F) r) := by
    have hodeDivf : ∀ r ∈ Set.Ioo 0 R,
        ∃ u : ℝ, HasDerivAt (deriv f) u r ∧
          u + (((m + 1 : ℕ) : ℝ) + 1) / r * deriv f r -
            (((m + 1 : ℕ) : ℝ) + 1) / r ^ 2 * f r +
            (1 - f r ^ 2) * f r = 0 := by
      intro r hr
      exact ⟨f₂ r, hdf r hr.1,
        radialODEAt_divided_for_profile_flux m f r (f₂ r) hr.1
          (hode_f r hr.1)⟩
    have hodeDivF : ∀ r ∈ Set.Ioo 0 R,
        ∃ u : ℝ, HasDerivAt (deriv F) u r ∧
          u + (((m + 1 : ℕ) : ℝ) + 1) / r * deriv F r -
            (((m + 1 : ℕ) : ℝ) + 1) / r ^ 2 * F r +
            (1 - F r ^ 2) * F r = 0 := by
      intro r hr
      exact ⟨F₂ r, hdF r hr.1,
        radialODEAt_divided_for_profile_flux m F r (F₂ r) hr.1
          (hode_F r hr.1)⟩
    have hpair := ratio_ordering_profiles (m + 1)
      (f := f) (F := F) (k := k₀) (R := R)
      hR
      (by intro r _; exact hfDiff r)
      (by intro r _; exact hFDiff r)
      hkcont.continuousOn
      (by simpa only [show (m + 1) + 1 = m + 2 by omega] using
        hfluxcont R hR)
      (by intro r hr; exact hFpos r hr.1)
      (by intro r hr; simpa only [profileK] using hkevent r hr.1)
      hk0 hodeDivf hodeDivF
    constructor
    · exact hpair.1
    · intro r hr
      simpa only [profileK] using hpair.2 r hr
  constructor
  · intro r hr
    exact (hinterval r hr).1 r ⟨hr, le_rfl⟩
  · intro r hr
    exact (hinterval r hr).2 r ⟨hr, le_rfl⟩

/-- The global contact theorem with its auxiliary domain assembled from
ordinary profile bounds.  The barrier conclusions `F²≥y_F` and
`η<r/√2`, and the ratio-ordering conclusions `F<f`, `k'>0`, are named
separately so they can be supplied by their dedicated profile theorems. -/
theorem profileContact_positive_from_assembled_bounds
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ)
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hforder : ∀ r, 0 < r → F r < f r)
    (hkderiv : ∀ r, 0 < r → 0 < deriv (profileK f F) r)
    (hyfpos : ∀ r, 0 < r → 0 < profileY f r)
    (hyFlt : ∀ r, 0 < r → profileY F r < 1)
    (hbarrier : ∀ r, 0 < r →
      0 ≤ F r ^ 2 - profileY F r)
    (hetaSmall : ∀ r, 0 < r →
      profileEta f F r < r / Real.sqrt 2)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r, 0 < r → HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r, 0 < r → HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (F r) (deriv F r) (F₂ r))
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → 0 < profileContactResidual f F r) :
    ∀ r, 0 < r → 0 < profileContactResidual f F r := by
  have hkgt : ∀ r, 0 < r → 1 < profileK f F r := by
    intro r hr
    unfold profileK
    exact (lt_div_iff₀ (hFpos r hr)).2 (by simpa using hforder r hr)
  have hMpos : ∀ r, 0 < r → 0 < profileM f F r := by
    intro r hr
    have hk := hkgt r hr
    unfold profileM ratioM
    nlinarith
  have haux : ∀ r, 0 < r → ∃ X : ℝ,
      0 < profileY F r ∧ profileY F r < 1 ∧
      0 < profileK f F r ∧ 0 < profileEta f F r ∧
      profileEta f F r ^ 2 < r ^ 2 / 2 ∧
      0 < X ∧ X < 1 ∧
      profileM f F r * profileEta f F r =
        profileK f F r * X * profileY F r ∧
      profileY F r ≤ F r ^ 2 := by
    intro r hr
    obtain ⟨X, q, _, hy0, hy1, hk0, heta0, hetaSq,
      hX0, hX1, hchi, hq, htrel⟩ :=
      contact_bounds_from_profile_inequalities f F r
        (deriv f r) (deriv F r) hr (hFpos r hr)
        (hkgt r hr) (hkderiv r hr) (hyfpos r hr)
        (hyFlt r hr) (by linarith [hbarrier r hr])
        (hetaSmall r hr) (hfDiff r).hasDerivAt
        (hFDiff r).hasDerivAt
    have hqeq : q = F r ^ 2 := by
      have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr)
      have hfactor : r ^ 2 * (F r ^ 2 - q) = 0 := by
        unfold profileT at htrel
        nlinarith [htrel]
      have hdiff : F r ^ 2 - q = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hr2
      linarith
    rw [hqeq] at hq
    exact ⟨X, hy0, hy1, hk0, heta0, hetaSq,
      hX0, hX1, hchi, hq⟩
  exact profileContact_positive_on_positive_axis m f F f₂ F₂
    hFpos hMpos hfDiff hFDiff hdf hdF hode_f hode_F haux hnear

/-- The slope-flux theorem removes `y_f>0` as an independent hypothesis.
The regular-origin flux continuity and `0<f<1` are visible inputs. -/
theorem profileContact_positive_from_slope_flux_bounds
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ)
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hforder : ∀ r, 0 < r → F r < f r)
    (hkderiv : ∀ r, 0 < r → 0 < deriv (profileK f F) r)
    (hfpos : ∀ r, 0 < r → 0 < f r)
    (hflt : ∀ r, 0 < r → f r < 1)
    (hslopeFluxCont : ∀ R, 0 < R →
      ContinuousOn (slopeFlux (m + 2) f) (Set.Icc 0 R))
    (hyFlt : ∀ r, 0 < r → profileY F r < 1)
    (hbarrier : ∀ r, 0 < r →
      0 ≤ F r ^ 2 - profileY F r)
    (hetaSmall : ∀ r, 0 < r →
      profileEta f F r < r / Real.sqrt 2)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r, 0 < r → HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r, 0 < r → HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (F r) (deriv F r) (F₂ r))
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → 0 < profileContactResidual f F r) :
    ∀ r, 0 < r → 0 < profileContactResidual f F r := by
  have hyfpos := profileY_pos_from_slope_flux m f f₂ hfDiff
    hslopeFluxCont hfpos hflt hdf hode_f
  exact profileContact_positive_from_assembled_bounds m f F f₂ F₂
    hFpos hforder hkderiv hyfpos hyFlt hbarrier hetaSmall
    hfDiff hFDiff hdf hdF hode_f hode_F hnear

/-- The verified profile barrier supplies the `F²≥y_F` input of the
assembled contact theorem.  The auxiliary `y` is an analytic extension
agreeing with the literal quotient only at positive radii. -/
theorem profileY_le_F_sq_from_barrier_theorem
    (m : ℕ) (F y F₂ : ℝ → ℝ)
    (hFdiff : Differentiable ℝ F)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r, 0 < r → y r = profileY F r)
    (hnear : ∃ ε : ℝ, 0 < ε ∧
      ∀ r, 0 < r → r < ε → 0 < F r ^ 2 - y r)
    (hfar : ∃ R : ℝ, ∀ r, R ≤ r → 0 < F r ^ 2 - y r)
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hFlt : ∀ r, 0 < r → F r < 1)
    (hdF : ∀ r, 0 < r → HasDerivAt (deriv F) (F₂ r) r)
    (hode_F : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (F r) (deriv F r) (F₂ r)) :
    ∀ r, 0 < r → 0 ≤ F r ^ 2 - profileY F r := by
  have hn : (3 : ℝ) ≤ (m : ℝ) + 3 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hODE : ∀ r, 0 < r →
      ∃ u : ℝ,
        HasDerivAt (deriv F) u r ∧
        radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r) u := by
    intro r hr
    exact ⟨F₂ r, hdF r hr, hode_F r hr⟩
  have hbarrier := profile_barrier_from_radial_ODE hn
    hFdiff hyDiff hyMatch hnear hfar hFpos hFlt hODE
  intro r hr
  rw [← hyMatch r hr]
  exact hbarrier r hr

/-- The verified global first-contact barrier supplies `η<r/√2` at every
positive radius.  Its continuity and near-origin start are explicit inputs. -/
theorem profileEta_lt_half_radius_from_barrier_theorem
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ)
    (hηcont : ∀ R, 0 < R →
      ContinuousOn (profileEta f F) (Set.Icc 0 R))
    (hnear : ∃ δ : ℝ, 0 < δ ∧
      ∀ r, 0 < r → r < δ →
        profileEta f F r < r / Real.sqrt 2)
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hFlt : ∀ r, 0 < r → F r < 1)
    (hkpos : ∀ r, 0 < r → 0 < profileK f F r)
    (hMpos : ∀ r, 0 < r → 0 < profileM f F r)
    (hylt : ∀ r, 0 < r → profileY F r < 1)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r, 0 < r → HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r, 0 < r → HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (F r) (deriv F r) (F₂ r)) :
    ∀ R, 0 < R → profileEta f F R < R / Real.sqrt 2 := by
  intro R hR
  have hprofiles : ∀ r ∈ Set.Ioc 0 R,
      ∃ f₁ F₁ f₂' F₂' : ℝ,
        HasDerivAt f f₁ r ∧ HasDerivAt F F₁ r ∧
        HasDerivAt (deriv f) f₂' r ∧
        HasDerivAt (deriv F) F₂' r ∧
        radialODEAt ((m : ℝ) + 3) r (f r) f₁ f₂' ∧
        radialODEAt ((m : ℝ) + 3) r (F r) F₁ F₂' := by
    intro r hr
    exact ⟨deriv f r, deriv F r, f₂ r, F₂ r,
      (hfDiff r).hasDerivAt, (hFDiff r).hasDerivAt,
      hdf r hr.1, hdF r hr.1,
      hode_f r hr.1, hode_F r hr.1⟩
  have hinterval := profile_eta_barrier_on_positive_interval
    m f F R hR (hηcont R hR) hnear
    (by intro r hr; exact hFpos r hr.1)
    (by intro r hr; exact hFlt r hr.1)
    (by intro r hr; exact hkpos r hr.1)
    (by intro r hr; exact hMpos r hr.1)
    (by intro r hr; exact hylt r hr.1)
    hfDiff hFDiff hprofiles
  exact hinterval R ⟨hR, le_rfl⟩

end

end BrezisOP6
