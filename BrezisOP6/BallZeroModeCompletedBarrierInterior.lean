import BrezisOP6.BallZeroModeCompletedBarrier
import BrezisOP6.BallZeroModeInterior
import BrezisOP6.OriginTaylorInterior
import BrezisOP6.OriginRatioGlobalProfile
import BrezisOP6.EtaInterior
import BrezisOP6.PositiveRadiusProfileUniqueness
import BrezisOP6.BallZeroModeInteriorAutoIntegrability

/-!
# Completed finite-ball barrier with interior profile equations

All uses of the finite-ball second-order equations take place strictly
inside the ball.  At the outer sphere the Picone argument uses continuous
traces of its flux and contact residual.  The entire-space profile equation
remains global, as it is needed for the far-field amplitude barrier.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

theorem ball_zero_mode_nonnegative_with_completed_profile_barrier_interior
    (m : ℕ) (f F y k₀ b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r)
    (hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) R))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Icc (0 : ℝ) R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R))
    (hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Icc (0 : ℝ) R))
    (hyFlt : ∀ r ∈ Ioc (0 : ℝ) R, profileY F r < 1)
    (hFone : Tendsto F atTop (𝓝 (1 : ℝ)))
    (hF2diffAll : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r, 0 < r → y r = profileY F r)
    (hFposAll : ∀ r, 0 < r → 0 < F r)
    (hFltAll : ∀ r, 0 < r → F r < 1)
    (hFodeAll : ∀ r, 0 < r →
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hηcont : ContinuousOn (profileEta f F) (Icc (0 : ℝ) R))
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
    (hScont : Tendsto (profileContactResidual f F)
      (𝓝[<] R) (𝓝 (profileContactResidual f F R)))
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R)
    (hflux_cont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F b)
        (uIcc δ R))
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        MeasureTheory.volume δ R)
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r := by
  have hn : 3 ≤ m + 3 := by omega
  have hnreal : (3 : ℝ) ≤ (m : ℝ) + 3 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hodeAllNat : ∀ r, 0 < r →
      radialODEAt ((m + 3 : ℕ) : ℝ) r
        (F r) (deriv F r) (deriv (deriv F) r) := by
    intro r hr
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hFodeAll r hr
  have hodeDivAll : ∀ r, 0 < r →
      radialGLResidual ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r) = 0 := by
    intro r hr
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (F r) (deriv F r) (deriv (deriv F) r) hr).mp
      (hFodeAll r hr)
    simpa only [radialGLResidual] using h
  have hinfty : Tendsto
      (fun r => F r / slopeBarrier ((m : ℝ) + 3) r)
      atTop (𝓝 (1 : ℝ)) := by
    have hslope := slopeBarrier_tendsto_one ((m : ℝ) + 3) hnreal
    convert hFone.div hslope (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hFC2 : ContDiffOn ℝ 2 F (Ioi (0 : ℝ)) :=
    radial_profile_contDiffOn_two_of_ode ((m : ℝ) + 3) F
      hFDiff hF2diffAll hFodeAll
  have hαsq : 1 / (((m : ℝ) + 3) + 2) < α ^ 2 :=
    entire_profile_initial_slope_gt_of_taylor hnreal hα
      hFposAll hFC2 (hFTaylor.toGlobal hR) hinfty hodeDivAll
  have hnearW : ∃ ε : ℝ, 0 < ε ∧
      ∀ r, 0 < r → r < ε → 0 < F r ^ 2 - y r := by
    obtain ⟨ε, hε, hsmall⟩ := original_profile_W_pos_near_origin
      hnreal hα hαsq (hFTaylor.toGlobal hR) hodeDivAll
    refine ⟨ε, hε, ?_⟩
    intro r hr hrε
    rw [hyMatch r hr]
    exact hsmall r hr hrε
  have hbarrierAll := profile_barrier_from_ode_with_origin_start
    (m + 3) (F := F) (y := y) hn hFone hFDiff hF2diffAll
    hyDiff hyMatch hnearW hFposAll hFltAll hodeAllNat
  have hbarrier : ∀ r ∈ Ioc (0 : ℝ) R,
      0 ≤ F r ^ 2 - profileY F r := by
    intro r hr
    simpa only [hyMatch r hr.1] using hbarrierAll r hr.1
  have hunique_origin : k₀ 0 = 1 →
      ∀ r ∈ Ioc (0 : ℝ) R, k₀ r = 1 :=
    ratio_origin_one_implies_identically_one_of_regular_ode_uniqueness
      m f F k₀ f₂ F₂ R α AF BF hR hα hFTaylor hFpos
      hkcont hkevent hRatioFluxCont hfDiff hFDiff hdf hdF
      hode_f hode_F
      (radial_profile_positive_radius_ivp_unique
        m f F f₂ F₂ R hfDiff hFDiff hdf hdF hode_f hode_F)
  have hk0 := profile_initial_ratio_gt_one_from_terminal
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
    hFpos hkevent hkpos hterminal hunique_origin hfDiff hFDiff
    hdf hdF hode_f hode_F
  have hβα : α < β := initial_slope_order_from_origin_ratio
    hR hα (hfTaylor.toClosed hR) (hFTaylor.toClosed hR)
    hkcont hkevent hk0
  have horder := profile_ratio_ordering_on_ball_from_flux
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont hFpos
    hkevent hk0 hfDiff hFDiff hdf hdF hode_f hode_F
  have hMpos : ∀ r ∈ Ioc (0 : ℝ) R,
      0 < profileM f F r := by
    intro r hr
    have hk : 1 < profileK f F r := by
      unfold profileK
      exact (lt_div_iff₀ (hFpos r hr)).mpr
        (by simpa using horder.1 r hr)
    unfold profileM ratioM
    nlinarith
  have hRhalf : 0 < R / 2 := by linarith
  have hhalflt : R / 2 < R := by linarith
  have hodeDivfHalf : ∀ r, 0 < r → r ≤ R / 2 →
      radialGLResidual ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r) = 0 := by
    intro r hr hrhalf
    have hrOpen : r ∈ Ioo (0 : ℝ) R :=
      ⟨hr, lt_of_le_of_lt hrhalf hhalflt⟩
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (f r) (deriv f r) (f₂ r) hr).mp (hode_f r hrOpen)
    simpa only [radialGLResidual, (hdf r hrOpen).deriv] using h
  have hodeDivFHalf : ∀ r, 0 < r → r ≤ R / 2 →
      radialGLResidual ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r) = 0 := by
    intro r hr _
    exact hodeDivAll r hr
  have hnearEta := original_profiles_eta_lt_linear_near_origin_on
    hnreal hRhalf hα hβα (hfTaylor.toGlobal hR)
    (hFTaylor.toGlobal hR)
    (fun r _ _ => hfDiff r) (fun r _ _ => hFDiff r)
    hodeDivfHalf hodeDivFHalf
  have hkPos : ∀ r ∈ Ioo (0 : ℝ) R,
      0 < profileK f F r := by
    intro r hr
    exact div_pos (hfpos r ⟨hr.1, hr.2.le⟩)
      (hFpos r ⟨hr.1, hr.2.le⟩)
  have hetaSmall : ∀ r ∈ Ioo (0 : ℝ) R,
      profileEta f F r < r / Real.sqrt 2 := by
    apply profile_eta_barrier_on_open_interval m f F R
      hηcont hnearEta
      (fun r hr => hFpos r ⟨hr.1, hr.2.le⟩)
      (fun r hr => hFltAll r hr.1)
      hkPos
      (fun r hr => hMpos r ⟨hr.1, hr.2.le⟩)
      (fun r hr => hyFlt r ⟨hr.1, hr.2.le⟩)
      hfDiff hFDiff
    intro r hr
    exact ⟨deriv f r, deriv F r, f₂ r, F₂ r,
      (hfDiff r).hasDerivAt, (hFDiff r).hasDerivAt,
      hdf r hr, hdF r hr, hode_f r hr, hode_F r hr⟩
  have hyfpos := profileY_pos_on_ball_from_flux m f f₂ R hR
    hfDiff hSlopeFluxCont hfpos hflt hdf hode_f
  have haux : ∀ r ∈ Ioo (0 : ℝ) R, ∃ X : ℝ,
      0 < profileY F r ∧ profileY F r < 1 ∧
      0 < profileK f F r ∧ 0 < profileEta f F r ∧
      profileEta f F r ^ 2 < r ^ 2 / 2 ∧
      0 < X ∧ X < 1 ∧
      profileM f F r * profileEta f F r =
        profileK f F r * X * profileY F r ∧
      profileY F r ≤ F r ^ 2 := by
    intro r hr
    have hrC : r ∈ Ioc (0 : ℝ) R := ⟨hr.1, hr.2.le⟩
    have hkgt : 1 < profileK f F r := by
      unfold profileK
      exact (lt_div_iff₀ (hFpos r hrC)).mpr
        (by simpa using horder.1 r hrC)
    obtain ⟨X, q, _, hy0, hy1, hk0', heta0, hetaSq,
      hX0, hX1, hchi, hq, htrel⟩ :=
      contact_bounds_from_profile_inequalities f F r
        (deriv f r) (deriv F r) hr.1 (hFpos r hrC)
        hkgt (horder.2 r hrC) (hyfpos r hrC)
        (hyFlt r hrC) (by linarith [hbarrier r hrC])
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
    exact ⟨X, hy0, hy1, hk0', heta0, hetaSq,
      hX0, hX1, hchi, hq⟩
  have hnearRaw := original_profiles_contact_pos_near_origin_on
    hnreal hRhalf hα hβα (hfTaylor.toGlobal hR)
    (hFTaylor.toGlobal hR)
    (fun r _ _ => hfDiff r) (fun r _ _ => hFDiff r)
    hodeDivfHalf hodeDivFHalf
  have hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r := by
    obtain ⟨ρ, hρ, hsmall⟩ := hnearRaw
    exact ⟨ρ, hρ, by
      intro r hr hrρ _
      simpa only [profileContactResidual] using hsmall r hr hrρ⟩
  have hfactor := original_profiles_origin_factor_tendsto_zero_on_ball
    hnreal hRhalf hα hβα (hfTaylor.toGlobal hR)
    (hFTaylor.toGlobal hR)
    (fun r _ _ => hfDiff r) (fun r _ _ => hFDiff r)
    hodeDivfHalf hodeDivFHalf
  exact ball_zero_mode_nonnegative_of_contact_domain_auto_integrability_interior
    m f F b db f₂ F₂ R hR hFpos hMpos hfDiff hFDiff
    hdf hdF hode_f hode_F haux hnear hScont
    hb hbR hDint hflux_cont hflux_int
    hfactor hblim

end

end BrezisOP6
