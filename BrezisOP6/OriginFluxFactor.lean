import BrezisOP6.OriginProfiles
import BrezisOP6.ZeroModeEndpoint

/-!
# The actual Picone flux factor at the radial origin

The weight `(f²-F²)/r²` has a finite nonzero limit, while the multiplier's
logarithmic slope tends to zero.  Their product therefore has a one-sided
zero limit, exactly the endpoint input of the zero-mode Picone theorem.
-/

namespace BrezisOP6

open Filter Topology

noncomputable section

/-- Convert the `t=rF` origin limit to the ordinary initial slope. -/
theorem profile_div_radius_origin_limit
    {F : ℝ → ℝ} {α A B : ℝ}
    (hF : RadialOriginTaylor F α A B) :
    Tendsto (fun r => F r / r) (𝓝[>] (0 : ℝ)) (𝓝 α) := by
  have ht := profileT_origin_limit hF
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      F r / r = profileT F r / r ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hrpos
    have hr : 0 < r := hrpos
    unfold profileT
    field_simp [ne_of_gt hr]
  exact (tendsto_congr' heq).2 ht

/-- The ratio of the original profiles tends to the ratio of their
positive initial slopes. -/
theorem profileK_origin_limit
    {f F : ℝ → ℝ} {α β Af Bf AF BF : ℝ}
    (hα : 0 < α)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF) :
    Tendsto (profileK f F) (𝓝[>] (0 : ℝ)) (𝓝 (β / α)) := by
  have hfLim := profile_div_radius_origin_limit hf
  have hFLim := profile_div_radius_origin_limit hF
  have hFrpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < F r / r :=
    hFLim.eventually (eventually_gt_nhds hα)
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileK f F r = (f r / r) / (F r / r) := by
    filter_upwards [self_mem_nhdsWithin, hFrpos]
      with r hrpos hFrpos'
    have hr : 0 < r := hrpos
    have hFpos : 0 < F r := (div_pos_iff_of_pos_right hr).mp hFrpos'
    unfold profileK
    field_simp [ne_of_gt hr, ne_of_gt hFpos]
  exact (tendsto_congr' heq).2
    (hfLim.div hFLim (ne_of_gt hα))

/-- The strict initial ratio inequality means exactly that the finite-ball
initial slope exceeds the entire-space initial slope.  The ratio extension
is needed only on `[0,R]`. -/
theorem initial_slope_order_from_origin_ratio
    {f F k₀ : ℝ → ℝ} {α β Af Bf AF BF R : ℝ}
    (hR : 0 < R) (hα : 0 < α)
    (hf : RadialOriginTaylorOn f β Af Bf R)
    (hF : RadialOriginTaylorOn F α AF BF R)
    (hkcont : ContinuousOn k₀ (Set.Icc 0 R))
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hk0 : 1 < k₀ 0) : α < β := by
  have hKlim := profileK_origin_limit hα
    (hf.toGlobal hR) (hF.toGlobal hR)
  have hEq : k₀ =ᶠ[𝓝[>] (0 : ℝ)] profileK f F := by
    filter_upwards [Ioc_mem_nhdsGT hR] with r hr
    exact (hkevent r hr).eq_of_nhds
  have hwithin : (𝓝[>] (0 : ℝ)) ≤
      (𝓝[Set.Icc (0 : ℝ) R] (0 : ℝ)) :=
    nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT hR)
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 R := ⟨le_rfl, hR.le⟩
  have hK0lim : Tendsto k₀ (𝓝[>] (0 : ℝ)) (𝓝 (k₀ 0)) :=
    (hkcont.continuousWithinAt h0mem).tendsto.mono_left hwithin
  have hK0lim' : Tendsto k₀ (𝓝[>] (0 : ℝ)) (𝓝 (β / α)) :=
    (tendsto_congr' hEq).2 hKlim
  have hratio : k₀ 0 = β / α :=
    tendsto_nhds_unique hK0lim hK0lim'
  rw [hratio] at hk0
  simpa only [one_mul] using (lt_div_iff₀ hα).mp hk0

/-- The unscaled logarithmic slope deficit vanishes at the origin. -/
theorem profileY_origin_zero
    {F : ℝ → ℝ} {C : ℝ}
    (hY : Tendsto (fun r => profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 C)) :
    Tendsto (profileY F) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have h := hY.mul (hr.pow 2)
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileY F r = (profileY F r / r ^ 2) * r ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hrpos
    have hrpos' : 0 < r := hrpos
    field_simp [ne_of_gt hrpos']
  simpa using (tendsto_congr' heq).2 h

/-- The unscaled interaction variable vanishes at the origin. -/
theorem profileEta_origin_zero
    {f F : ℝ → ℝ} {C : ℝ}
    (hEta : Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 C)) :
    Tendsto (profileEta f F) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have h := hEta.mul (hr.pow 4)
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileEta f F r = (profileEta f F r / r ^ 4) * r ^ 4 := by
    filter_upwards [self_mem_nhdsWithin] with r hrpos
    have hrpos' : 0 < r := hrpos
    field_simp [ne_of_gt hrpos']
  simpa using (tendsto_congr' heq).2 h

/-- The actual combined Picone flux factor tends to zero using only
the four natural scaled origin limits. -/
theorem profilePiconeOriginFactor_tendsto_zero
    {f F : ℝ → ℝ} {α β CY CE : ℝ}
    (hf : Tendsto (fun r => f r / r) (𝓝[>] (0 : ℝ)) (𝓝 β))
    (hF : Tendsto (fun r => F r / r) (𝓝[>] (0 : ℝ)) (𝓝 α))
    (hk : Tendsto (profileK f F) (𝓝[>] (0 : ℝ)) (𝓝 (β / α)))
    (hY : Tendsto (fun r => profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 CY))
    (hEta : Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 CE)) :
    Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hwraw := (hf.pow 2).sub (hF.pow 2)
  have hweight : Tendsto (piconeWeightFromProfiles f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (β ^ 2 - α ^ 2)) := by
    have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        piconeWeightFromProfiles f F r =
          (f r / r) ^ 2 - (F r / r) ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with r hrpos
      have hr : 0 < r := hrpos
      unfold piconeWeightFromProfiles
      field_simp [ne_of_gt hr]
    exact (tendsto_congr' heq).2 hwraw
  have hyZero := profileY_origin_zero hY
  have hetaZero := profileEta_origin_zero hEta
  have hpsi : Tendsto
      (fun r => piconeMultiplierLogSlope
        (profileY F r) (profileK f F r) (profileEta f F r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hraw := (hyZero.add (hk.mul hetaZero)).neg
    simpa only [piconeMultiplierLogSlope, mul_zero, zero_add,
      neg_zero] using hraw
  have hproduct := hweight.mul hpsi
  simpa only [profilePiconeOriginFactor, mul_zero] using hproduct

/-- With the actual differentiated profile expansions, the zero-mode
origin flux condition is a theorem, not a separate assumption. -/
theorem original_profiles_origin_factor_tendsto_zero
    {n α β Af Bf AF BF : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF)
    (hfdiff : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact profilePiconeOriginFactor_tendsto_zero
    (profile_div_radius_origin_limit hf)
    (profile_div_radius_origin_limit hF)
    (profileK_origin_limit hα hf hF)
    (profileY_origin_limit hn hα hF hFODE)
    (profileEta_origin_limit hn hα hβα hf hF hfdiff hFdiff
      hfODE hFODE)

/-- The finite-ball version uses the original ODE only on `(0,R]`.
It directly supplies the endpoint hypothesis of `BallZeroMode`. -/
theorem original_profiles_origin_factor_tendsto_zero_on_ball
    {n α β Af Bf AF BF R : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF)
    (hfdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact profilePiconeOriginFactor_tendsto_zero
    (profile_div_radius_origin_limit hf)
    (profile_div_radius_origin_limit hF)
    (profileK_origin_limit hα hf hF)
    (profileY_origin_limit_on hn hR hα hF hFODE)
    (profileEta_origin_limit_on hn hR hα hβα hf hF hfdiff
      hFdiff hfODE hFODE)

/-- A locally stated Taylor expansion on the finite ball is sufficient
for the origin flux factor; no Taylor identity is imposed beyond `R`. -/
theorem original_profiles_origin_factor_tendsto_zero_on_ball_localTaylor
    {n α β Af Bf AF BF R : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylorOn f β Af Bf R)
    (hF : RadialOriginTaylorOn F α AF BF R)
    (hfdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact profilePiconeOriginFactor_tendsto_zero
    (profile_div_radius_origin_limit (hf.toGlobal hR))
    (profile_div_radius_origin_limit (hF.toGlobal hR))
    (profileK_origin_limit hα (hf.toGlobal hR) (hF.toGlobal hR))
    (profileY_origin_limit_on_localTaylor hn hR hα hF hFODE)
    (profileEta_origin_limit_on_localTaylor hn hR hα hβα hf hF
      hfdiff hFdiff hfODE hFODE)

end

end BrezisOP6
