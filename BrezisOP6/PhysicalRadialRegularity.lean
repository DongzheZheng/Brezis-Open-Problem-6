import BrezisOP6.OriginProfiles
import BrezisOP6.OriginFluxFactor
import BrezisOP6.OriginTaylorInterior
import BrezisOP6.ProfileContactFromODE

/-!
# Redundant regularity data for the physical radial profiles

The public profile package currently records `C²` regularity of each
profile together with `C¹` regularity of its derivative, pointwise second
derivatives, and auxiliary second-derivative functions.  The latter are
consequences of the former.  These lemmas give a canonical choice of the
second-derivative witnesses without adding an analytic input.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

/-- Global `C²` regularity already includes global `C¹` regularity of the
first derivative. -/
theorem radial_profile_deriv_contDiff_one
    (p : ℝ → ℝ) (hp : ContDiff ℝ 2 p) :
    ContDiff ℝ 1 (deriv p) := by
  have hp' : ContDiff ℝ (1 + 1) p := by simpa using hp
  exact (contDiff_succ_iff_deriv.mp hp').2.2

/-- A canonical second-derivative witness at every radius. -/
theorem radial_profile_deriv_hasDerivAt
    (p : ℝ → ℝ) (hp : ContDiff ℝ 2 p) (r : ℝ) :
    HasDerivAt (deriv p) (deriv (deriv p) r) r :=
  (radial_profile_deriv_contDiff_one p hp).differentiable_one r |>.hasDerivAt

/-- In particular, the separate positive-radius differentiability field
is redundant once the profile is globally `C²`. -/
theorem radial_profile_deriv_differentiable_positive
    (p : ℝ → ℝ) (hp : ContDiff ℝ 2 p) :
    ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv p) r := by
  intro r _
  exact (radial_profile_deriv_hasDerivAt p hp r).differentiableAt

/-- For the canonical second-derivative witnesses, the several profile
ODE hypotheses are restrictions of a single pointwise ODE. -/
theorem radial_profile_ode_with_canonical_second
    (n R : ℝ) (p : ℝ → ℝ)
    (hODE : ∀ r : ℝ, 0 < r →
      radialODEAt n r (p r) (deriv p r) (deriv (deriv p) r)) :
    (∀ r ∈ Set.Ioo (0 : ℝ) R,
      radialODEAt n r (p r) (deriv p r) (deriv (deriv p) r)) ∧
    (∀ r : ℝ, 0 < r → r < R →
      radialODEAt n r (p r) (deriv p r) (deriv (deriv p) r)) := by
  constructor
  · intro r hr
    exact hODE r hr.1
  · intro r hr _
    exact hODE r hr

/-- The quotient-interaction variable has a continuous extension over
the radial origin once the two profiles have their regular Taylor data,
solve the ODE near zero, and are strictly ordered.  Its value at zero is
the value of the literal Lean expression, namely zero. -/
theorem physical_profile_eta_continuousOn
    (m : ℕ) (f F : ℝ → ℝ)
    (R α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α) (hαβ : α < β)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hfC2 : ContDiff ℝ 2 f) (hFC2 : ContDiff ℝ 2 F)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (horder : ∀ r ∈ Ioc (0 : ℝ) R, F r < f r)
    (hfODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r))
    (hFODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r)) :
    ContinuousOn (profileEta f F) (Icc (0 : ℝ) R) := by
  let R₀ : ℝ := R / 2
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  have hR₀lt : R₀ < R := by dsimp [R₀]; linarith
  have hfTaylor₀ : RadialOriginTaylorOn f β Af Bf R₀ :=
    { e₀ := hfTaylor.e₀
      e₁ := hfTaylor.e₁
      e₂ := hfTaylor.e₂
      value := by
        intro r hr hrR₀
        exact hfTaylor.value r hr (lt_of_le_of_lt hrR₀ hR₀lt)
      first := by
        intro r hr hrR₀
        exact hfTaylor.first r hr (lt_of_le_of_lt hrR₀ hR₀lt)
      second := by
        intro r hr hrR₀
        exact hfTaylor.second r hr (lt_of_le_of_lt hrR₀ hR₀lt)
      e₀_zero := hfTaylor.e₀_zero
      e₁_zero := hfTaylor.e₁_zero
      e₂_zero := hfTaylor.e₂_zero }
  have hFTaylor₀ : RadialOriginTaylorOn F α AF BF R₀ :=
    { e₀ := hFTaylor.e₀
      e₁ := hFTaylor.e₁
      e₂ := hFTaylor.e₂
      value := by
        intro r hr hrR₀
        exact hFTaylor.value r hr (lt_of_le_of_lt hrR₀ hR₀lt)
      first := by
        intro r hr hrR₀
        exact hFTaylor.first r hr (lt_of_le_of_lt hrR₀ hR₀lt)
      second := by
        intro r hr hrR₀
        exact hFTaylor.second r hr (lt_of_le_of_lt hrR₀ hR₀lt)
      e₀_zero := hFTaylor.e₀_zero
      e₁_zero := hFTaylor.e₁_zero
      e₂_zero := hFTaylor.e₂_zero }
  have hn : (3 : ℝ) ≤ (m : ℝ) + 3 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hηScaled : Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ))
      (𝓝 (α * β / (((m : ℝ) + 3) + 4))) := by
    apply profileEta_origin_limit_on_localTaylor hn hR₀ hα hαβ
      hfTaylor₀ hFTaylor₀
    · intro r _ _
      exact (hfC2.of_le (by norm_num)).differentiable_one r
    · intro r _ _
      exact (hFC2.of_le (by norm_num)).differentiable_one r
    · intro r hr hrR₀
      exact (radialODEAt_iff_divided _ _ _ _ _ hr).mp
        (hfODE r hr (lt_of_le_of_lt hrR₀ hR₀lt))
    · intro r hr hrR₀
      exact (radialODEAt_iff_divided _ _ _ _ _ hr).mp
        (hFODE r hr (lt_of_le_of_lt hrR₀ hR₀lt))
  have hηlim : Tendsto (profileEta f F)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := profileEta_origin_zero hηScaled
  have hfilter : 𝓝[Ioc (0 : ℝ) R] (0 : ℝ) = 𝓝[>] (0 : ℝ) := by
    apply le_antisymm
    · exact nhdsWithin_mono _ Ioc_subset_Ioi_self
    · exact nhdsWithin_le_iff.mpr (Ioc_mem_nhdsGT hR)
  have hcont₀ : ContinuousWithinAt (profileEta f F)
      (Icc (0 : ℝ) R) 0 := by
    have hcontRight : ContinuousWithinAt (profileEta f F)
        (Ioc (0 : ℝ) R) 0 := by
      change Tendsto (profileEta f F) (𝓝[Ioc (0 : ℝ) R] 0)
        (𝓝 (profileEta f F 0))
      rw [hfilter]
      simpa [profileEta] using hηlim
    have hset : insert (0 : ℝ) (Ioc (0 : ℝ) R) = Icc (0 : ℝ) R := by
      ext r
      simp only [mem_insert_iff, mem_Ioc, mem_Icc]
      constructor
      · rintro (rfl | ⟨hr, hrR⟩)
        · exact ⟨le_rfl, hR.le⟩
        · exact ⟨hr.le, hrR⟩
      · intro hr
        rcases eq_or_lt_of_le hr.1 with heq | hlt
        · exact Or.inl heq.symm
        · exact Or.inr ⟨hlt, hr.2⟩
    rw [← hset]
    exact continuousWithinAt_insert_self.mpr hcontRight
  intro r hr
  rcases eq_or_lt_of_le hr.1 with heq | hrpos
  · subst r
    exact hcont₀
  · have hFposr : 0 < F r := hFpos r ⟨hrpos, hr.2⟩
    have hKr : 1 < profileK f F r := by
      unfold profileK
      apply (lt_div_iff₀ hFposr).2
      simpa only [one_mul] using horder r ⟨hrpos, hr.2⟩
    have hMr : 0 < profileM f F r := by
      dsimp [profileM, ratioM]
      nlinarith
    have hfC1 : ContDiff ℝ 1 f := hfC2.of_le (by norm_num)
    have hFC1 : ContDiff ℝ 1 F := hFC2.of_le (by norm_num)
    have hkC1 : ContDiffAt ℝ 1 (profileK f F) r := by
      simpa only [profileK] using
        (hfC1.contDiffAt.div hFC1.contDiffAt (ne_of_gt hFposr))
    have hkCont : ContinuousAt (profileK f F) r := hkC1.continuousAt
    have hkDerCont : ContinuousAt (deriv (profileK f F)) r :=
      (hkC1.derivWithin (m := 0) (by norm_num)).continuousAt
    have hMCont : ContinuousAt (profileM f F) r := by
      simpa only [profileM, ratioM] using
        (hkCont.pow 2).sub continuousAt_const
    have hηCont : ContinuousAt (profileEta f F) r := by
      simpa only [profileEta] using
        (continuousAt_id.mul hkDerCont).div hMCont (ne_of_gt hMr)
    exact hηCont.continuousWithinAt

/-- The terminal contact residual has the required left limit as soon as
the actual profile variables are continuous on the closed ball.  This
removes the separate terminal-limit input from the radial package. -/
theorem physical_profile_contact_left_limit
    (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (hFR : 0 < F R)
    (hηcont : ContinuousOn (profileEta f F) (Icc (0 : ℝ) R)) :
    Tendsto (profileContactResidual f F)
      (𝓝[<] R) (𝓝 (profileContactResidual f F R)) := by
  have hRmem : R ∈ Icc (0 : ℝ) R := ⟨hR.le, le_rfl⟩
  have hfR : ContinuousAt f R := hfC1.continuous.continuousAt
  have hFRcont : ContinuousAt F R := hFC1.continuous.continuousAt
  have hdFR : ContinuousAt (deriv F) R :=
    hFC1.continuous_deriv_one.continuousAt
  have hK : ContinuousAt (profileK f F) R := by
    simpa only [profileK] using hfR.div hFRcont (ne_of_gt hFR)
  have hM : ContinuousAt (profileM f F) R := by
    simpa only [profileM, ratioM] using
      (hK.pow 2).sub continuousAt_const
  have hT : ContinuousAt (profileT F) R := by
    simpa only [profileT] using continuousAt_id.mul hFRcont
  have hY : ContinuousAt (profileY F) R := by
    simpa only [profileY] using
      continuousAt_const.sub
        ((continuousAt_id.mul hdFR).div hFRcont (ne_of_gt hFR))
  have hη : ContinuousWithinAt (profileEta f F)
      (Icc (0 : ℝ) R) R := hηcont R hRmem
  have hS : ContinuousWithinAt (profileContactResidual f F)
      (Icc (0 : ℝ) R) R := by
    dsimp only [profileContactResidual, contactResidual]
    have hId : ContinuousWithinAt (fun r : ℝ => r)
        (Icc (0 : ℝ) R) R := continuousAt_id.continuousWithinAt
    exact (((((hId.pow 2).add
      (hM.continuousWithinAt.mul (hT.continuousWithinAt.pow 2))).sub
      (continuousWithinAt_const.mul hY.continuousWithinAt)).sub
      (continuousWithinAt_const.mul (hY.continuousWithinAt.pow 2))).sub
      (hη.pow 2))
  exact hS.tendsto.mono_left
    (nhdsWithin_le_of_mem (Icc_mem_nhdsLT hR))

end

end BrezisOP6
