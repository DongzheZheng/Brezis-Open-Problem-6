import BrezisOP6.ProfileBarrierCompletion
import BrezisOP6.BallZeroModeFromOrigin
import BrezisOP6.OriginBarrierSigns
import BrezisOP6.EtaGlobal
import BrezisOP6.ProfileC2FromODE

/-!
# Finite-ball zero mode with the entire-profile amplitude barrier discharged

The global radial ODE and its regular-origin/far-field data imply the
`F² ≥ y_F` barrier.  The finite-ball Picone theorem then uses that result
without taking the barrier as a separate hypothesis.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

/-- The explicit comparison slope tends to one at spatial infinity. -/
theorem slopeBarrier_tendsto_one (n : ℝ) (hn : 3 ≤ n) :
    Filter.Tendsto (slopeBarrier n) Filter.atTop (𝓝 (1 : ℝ)) := by
  have hbase : Filter.Tendsto
      (fun r : ℝ => 1 + (n + 2) * r ^ (-2 : ℤ))
      Filter.atTop (𝓝 (1 : ℝ)) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := n + 2)).mul
        invSquare_tendsto_zero) using 1 <;> simp
  have hroot : Filter.Tendsto
      (fun r : ℝ => Real.sqrt (1 + (n + 2) * r ^ (-2 : ℤ)))
      Filter.atTop (𝓝 (1 : ℝ)) := by
    convert (Real.continuous_sqrt.tendsto 1).comp hbase using 1 <;> norm_num
  have hrecip : Filter.Tendsto
      (fun r : ℝ => (Real.sqrt (1 + (n + 2) * r ^ (-2 : ℤ)))⁻¹)
      Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa using hroot.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (slopeBarrier n) =ᶠ[Filter.atTop]
      (fun r : ℝ =>
        (Real.sqrt (1 + (n + 2) * r ^ (-2 : ℤ)))⁻¹) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    have hrne : r ≠ 0 := ne_of_gt hr
    have hD : 0 < r ^ 2 + n + 2 := by nlinarith [sq_nonneg r]
    have hT : 0 < 1 + (n + 2) * r ^ (-2 : ℤ) := by
      have hi : 0 ≤ r ^ (-2 : ℤ) := by positivity
      nlinarith
    have hDs : (Real.sqrt (r ^ 2 + n + 2)) ^ 2 =
        r ^ 2 + n + 2 := Real.sq_sqrt (le_of_lt hD)
    have hTs : (Real.sqrt (1 + (n + 2) * r ^ (-2 : ℤ))) ^ 2 =
        1 + (n + 2) * r ^ (-2 : ℤ) := Real.sq_sqrt (le_of_lt hT)
    have hL : 0 ≤ slopeBarrier n r := by
      unfold slopeBarrier
      positivity
    have hU : 0 ≤ (Real.sqrt (1 + (n + 2) * r ^ (-2 : ℤ)))⁻¹ := by
      positivity
    have hsq : (slopeBarrier n r) ^ 2 =
        ((Real.sqrt (1 + (n + 2) * r ^ (-2 : ℤ)))⁻¹) ^ 2 := by
      unfold slopeBarrier
      rw [div_pow, hDs, inv_pow, hTs]
      simp only [zpow_neg]
      field_simp [hrne, ne_of_gt hD]
      ring
    nlinarith [hsq]
  exact (tendsto_congr' heq).2 hrecip

theorem ball_zero_mode_nonnegative_with_completed_profile_barrier
    (m : ℕ) (f F y k₀ b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hfTaylor : RadialOriginTaylorOn f β Af Bf R)
    (hFTaylor : RadialOriginTaylorOn F α AF BF R)
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
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hF2diffAll : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r, 0 < r → y r = profileY F r)
    (hFposAll : ∀ r, 0 < r → 0 < F r)
    (hFltAll : ∀ r, 0 < r → F r < 1)
    (hFodeAll : ∀ r, 0 < r →
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hηcont : ContinuousOn (profileEta f F) (Set.Icc 0 R))
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
    (hb : ∀ r ∈ Set.Ioc 0 R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R)
    (hsq_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        MeasureTheory.volume δ R)
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        MeasureTheory.volume δ R)
    (hrem_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
        MeasureTheory.volume δ R)
    (hbcont : ContinuousAt b 0) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r := by
  have hn : 3 ≤ m + 3 := by omega
  have hodeAllNat : ∀ r, 0 < r →
      radialODEAt ((m + 3 : ℕ) : ℝ) r
        (F r) (deriv F r) (deriv (deriv F) r) := by
    intro r hr
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hFodeAll r hr
  have hnreal : (3 : ℝ) ≤ (m : ℝ) + 3 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hodeDivAll : ∀ r, 0 < r →
      radialGLResidual ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r) = 0 := by
    intro r hr
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (F r) (deriv F r) (deriv (deriv F) r) hr).mp
      (hFodeAll r hr)
    simpa only [radialGLResidual] using h
  have hinfty : Filter.Tendsto
      (fun r => F r / slopeBarrier ((m : ℝ) + 3) r)
      Filter.atTop (𝓝 (1 : ℝ)) := by
    have hslope := slopeBarrier_tendsto_one ((m : ℝ) + 3) hnreal
    convert hFone.div hslope (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hFC2 : ContDiffOn ℝ 2 F (Set.Ioi 0) :=
    radial_profile_contDiffOn_two_of_ode ((m : ℝ) + 3) F
      hFDiff hF2diffAll hFodeAll
  have hαsq : 1 / (((m : ℝ) + 3) + 2) < α ^ 2 :=
    entire_profile_initial_slope_gt_of_taylor hnreal hα
      hFposAll hFC2 (hFTaylor.toGlobal hR) hinfty hodeDivAll
  have hodeDiv : ∀ r, 0 < r → r ≤ R →
      radialGLResidual ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r) = 0 := by
    intro r hr _
    exact hodeDivAll r hr
  have hnearRaw := original_profile_W_pos_near_origin_on_localTaylor
    hnreal hR hα hαsq hFTaylor hodeDiv
  have hnearW : ∃ ε : ℝ, 0 < ε ∧
      ∀ r, 0 < r → r < ε → 0 < F r ^ 2 - y r := by
    obtain ⟨ε, hε, hsmall⟩ := hnearRaw
    refine ⟨ε, hε, ?_⟩
    intro r hr hrε
    rw [hyMatch r hr]
    exact hsmall r hr hrε
  have hbarrierAll := profile_barrier_from_ode_with_origin_start
    (m + 3) (F := F) (y := y) hn hFone hFDiff hF2diffAll
    hyDiff hyMatch hnearW hFposAll hFltAll hodeAllNat
  have hbarrier : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ F r ^ 2 - profileY F r := by
    intro r hr
    simpa only [hyMatch r hr.1] using hbarrierAll r hr.1
  have hk0 := profile_initial_ratio_gt_one_from_terminal
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
    hFpos hkevent hkpos hterminal hunique_origin hfDiff hFDiff
    (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hdF r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_F r ⟨hr.1, hr.2.le⟩)
  have hβα : α < β := initial_slope_order_from_origin_ratio
    hR hα hfTaylor hFTaylor hkcont hkevent hk0
  have hodeDivf : ∀ r, 0 < r → r ≤ R →
      radialGLResidual ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r) = 0 := by
    intro r hr hrR
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (f r) (deriv f r) (f₂ r) hr).mp
      (hode_f r ⟨hr, hrR⟩)
    simpa only [radialGLResidual, (hdf r ⟨hr, hrR⟩).deriv] using h
  have hnearEta := original_profiles_eta_lt_linear_near_origin_on_localTaylor
    hnreal hR hα hβα hfTaylor hFTaylor
    (fun r _ _ => hfDiff r) (fun r _ _ => hFDiff r)
    hodeDivf hodeDiv
  have horder := (profile_ratio_ordering_on_ball_from_flux
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
    hFpos hkevent hk0 hfDiff hFDiff
    (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hdF r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_F r ⟨hr.1, hr.2.le⟩)).1
  have hkPos : ∀ r ∈ Set.Ioc 0 R,
      0 < profileK f F r := by
    intro r hr
    exact div_pos (hfpos r hr) (hFpos r hr)
  have hMpos : ∀ r ∈ Set.Ioc 0 R,
      0 < profileM f F r := by
    intro r hr
    have hk : 1 < profileK f F r := by
      unfold profileK
      exact (lt_div_iff₀ (hFpos r hr)).mpr (by simpa using horder r hr)
    unfold profileM ratioM
    nlinarith
  have hetaSmall : ∀ r ∈ Set.Ioc 0 R,
      profileEta f F r < r / Real.sqrt 2 := by
    apply profile_eta_barrier_on_positive_interval m f F R
      hR hηcont hnearEta hFpos
      (by intro r hr; exact hFltAll r hr.1)
      hkPos hMpos hyFlt hfDiff hFDiff
    intro r hr
    exact ⟨deriv f r, deriv F r, f₂ r, F₂ r,
      (hfDiff r).hasDerivAt, (hFDiff r).hasDerivAt,
      hdf r hr, hdF r hr, hode_f r hr, hode_F r hr⟩
  exact ball_zero_mode_nonnegative_from_origin_taylor
    m f F k₀ b db f₂ F₂ R α β Af Bf AF BF
    hR hα hfTaylor hFTaylor hFpos hfpos hflt hkcont hkevent
    hkpos hterminal hunique_origin hRatioFluxCont hSlopeFluxCont
    hyFlt hbarrier hetaSmall hfDiff hFDiff hdf hdF hode_f hode_F
    hb hbR hDint hsq_int hflux_int hrem_int hbcont

end

end BrezisOP6
