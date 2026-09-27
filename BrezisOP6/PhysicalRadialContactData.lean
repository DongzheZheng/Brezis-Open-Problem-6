import BrezisOP6.ActualSobolevClosureMain
import BrezisOP6.PhysicalProfileContactCertificate

/-!
# Contact certificate from the public physical profile data

The public `PhysicalRadialData` contains the two cited radial profiles.
Their ordering, strict interior contact sign, and origin Picone flux
factor are consequences of the formalized profile comparison and barrier
theorems.  This module exposes those consequences for quantitative
annular estimates without adding them as new fields of the data record.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

theorem PhysicalRadialData.contact_coercivity_certificate
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R) :
    (∀ r ∈ Ioc (0 : ℝ) R, 0 < profileM p.f p.F r) ∧
    (∀ r ∈ Ioc (0 : ℝ) R,
      0 ≤ profileContactResidual p.f p.F r) ∧
    (∀ r ∈ Ioo (0 : ℝ) R,
      0 < profileContactResidual p.f p.F r) ∧
    Tendsto (profilePiconeOriginFactor p.f p.F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 p.F := p.hFC2.of_le (by norm_num)
  have hdfC1 : ContDiff ℝ 1 (deriv p.f) :=
    radial_profile_deriv_contDiff_one p.f p.hfC2
  have hdFC1 : ContDiff ℝ 1 (deriv p.F) :=
    radial_profile_deriv_contDiff_one p.F p.hFC2
  let f₂ : ℝ → ℝ := deriv (deriv p.f)
  let F₂ : ℝ → ℝ := deriv (deriv p.F)
  have hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv p.f) (f₂ r) r := by
    intro r _
    exact radial_profile_deriv_hasDerivAt p.f p.hfC2 r
  have hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv p.F) (F₂ r) r := by
    intro r _
    exact radial_profile_deriv_hasDerivAt p.F p.hFC2 r
  have hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (p.f r) (deriv p.f r) (f₂ r) := by
    intro r hr
    exact p.hfODE r hr.1 hr.2
  have hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (p.F r) (deriv p.F r) (F₂ r) := by
    intro r hr
    exact p.hFodeAll r hr.1
  have hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) p.f p.F)
      (Icc (0 : ℝ) R) := by
    have hraw : Continuous (fun r : ℝ =>
        r ^ (m + 2) *
          (p.F r * deriv p.f r - p.f r * deriv p.F r)) :=
      (continuous_id.pow (m + 2)).mul
        ((hFC1.continuous.mul hdfC1.continuous).sub
          (hfC1.continuous.mul hdFC1.continuous))
    simpa only [ratioFlux] using hraw.continuousOn
  have hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) p.f)
      (Icc (0 : ℝ) R) := by
    have hraw : Continuous (fun r : ℝ =>
        r ^ (m + 2) * (r * deriv p.f r - p.f r)) :=
      (continuous_id.pow (m + 2)).mul
        ((continuous_id.mul hdfC1.continuous).sub hfC1.continuous)
    simpa only [slopeFlux] using hraw.continuousOn
  let k₀ := physicalProfileRatioExtension p.f p.F p.α p.β
  have hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < p.F r := by
    intro r hr
    exact p.hFposAll r hr.1
  obtain ⟨hkcont, hkevent, hkpos⟩ :=
    physical_profile_ratio_extension_data
      p.f p.F R p.α p.β p.Af p.Bf p.AF p.BF
      p.hR p.hα p.hβ p.hfTaylor p.hFTaylor p.hfpos hFpos
      (fun r => hfC1.differentiable_one r)
      (fun r => hFC1.differentiable_one r)
  have hterminal : p.F R < p.f R := by
    rw [p.hfR]
    exact p.hFltAll R p.hR
  have horder : ∀ r ∈ Ioc (0 : ℝ) R, p.F r < p.f r :=
    (physical_radial_profiles_ordered_from_terminal
      m p.f p.F k₀ f₂ F₂ R p.α p.AF p.BF p.hR p.hα
      p.hFTaylor hFpos hkcont hkevent hkpos hterminal
      hRatioFluxCont
      (fun r => hfC1.differentiable_one r)
      (fun r => hFC1.differentiable_one r)
      hdf hdF hode_f hode_F).1
  have hαβ : p.α < p.β :=
    physical_radial_initial_slopes_ordered_from_terminal
      m p.f p.F k₀ f₂ F₂ R p.α p.β
      p.Af p.Bf p.AF p.BF p.hR p.hα
      p.hfTaylor p.hFTaylor hFpos hkcont hkevent hkpos
      hterminal hRatioFluxCont
      (fun r => hfC1.differentiable_one r)
      (fun r => hFC1.differentiable_one r)
      hdf hdF hode_f hode_F
  have hηcont : ContinuousOn (profileEta p.f p.F)
      (Icc (0 : ℝ) R) :=
    physical_profile_eta_continuousOn
      m p.f p.F R p.α p.β p.Af p.Bf p.AF p.BF
      p.hR p.hα hαβ p.hfTaylor p.hFTaylor
      p.hfC2 p.hFC2 hFpos horder
      p.hfODE (fun r hr _ => p.hFodeAll r hr)
  have hScont : Tendsto (profileContactResidual p.f p.F)
      (𝓝[<] R) (𝓝 (profileContactResidual p.f p.F R)) :=
    physical_profile_contact_left_limit
      p.f p.F R p.hR hfC1 hFC1
      (hFpos R ⟨p.hR, le_rfl⟩) hηcont
  exact physical_profile_contact_coercivity_certificate
    m p.f p.F p.y k₀ f₂ F₂ R
    p.α p.β p.Af p.Bf p.AF p.BF
    p.hR p.hα p.hfTaylor p.hFTaylor hFpos
    p.hfpos p.hflt hkcont hkevent hkpos hterminal
    hRatioFluxCont hSlopeFluxCont p.hyFlt p.hFone
    (radial_profile_deriv_differentiable_positive p.F p.hFC2)
    p.hyDiff p.hyMatch p.hFposAll p.hFltAll p.hFodeAll
    hηcont
    (fun r => hfC1.differentiable_one r)
    (fun r => hFC1.differentiable_one r)
    hdf hdF hode_f hode_F hScont

/-- The positivity of the certified ratio yields strict separation of the
two physical profiles and of their squared coefficients at every positive
radius in the ball. -/
theorem PhysicalRadialData.profile_gap_positive
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R) :
    ∀ r ∈ Ioc (0 : ℝ) R,
      0 < p.f r ^ 2 - p.F r ^ 2 := by
  intro r hr
  have hFpos : 0 < p.F r := p.hFposAll r hr.1
  have hfpos : 0 < p.f r := p.hfpos r hr
  have hM : 0 < profileM p.f p.F r :=
    (p.contact_coercivity_certificate m R).1 r hr
  have hratio : 1 < p.f r / p.F r := by
    dsimp [profileM, ratioM, profileK] at hM
    have hpos : 0 < p.f r / p.F r := div_pos hfpos hFpos
    nlinarith
  have horder : p.F r < p.f r := by
    have h := (lt_div_iff₀ hFpos).mp hratio
    simpa only [one_mul] using h
  nlinarith [mul_pos (sub_pos.mpr horder) (add_pos hfpos hFpos)]

theorem PhysicalRadialData.profile_order
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R) :
    ∀ r ∈ Ioc (0 : ℝ) R, p.F r < p.f r := by
  intro r hr
  have hFpos : 0 < p.F r := p.hFposAll r hr.1
  have hfpos : 0 < p.f r := p.hfpos r hr
  have hgap : 0 < p.f r ^ 2 - p.F r ^ 2 :=
    p.profile_gap_positive m R r hr
  by_contra hn
  have hle : p.f r ≤ p.F r := le_of_not_gt hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_pos hfpos hFpos).le]

end

end BrezisOP6
