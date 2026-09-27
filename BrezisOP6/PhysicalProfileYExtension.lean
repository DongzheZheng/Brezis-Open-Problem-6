import BrezisOP6.OriginFactorTaylor
import BrezisOP6.PhysicalRadialRegularity
import BrezisOP6.ActualSobolevClosureMain

/-!
# A differentiable whole-line representative of the profile slope defect

The physical profile is only needed at positive radius.  Its scalar slope
defect `1 - r F'(r) / F(r)` has a removable value at the radial origin when
`F(r) = r H(r²)` with `H(0) > 0`.  Extending it by zero on the nonpositive
half-line supplies the differentiable whole-line auxiliary function used by
the profile-flow argument, without assuming such an extension separately.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

/-- The slope defect on positive radii, with its removable origin value and
an arbitrary smooth continuation (zero) on negative radii. -/
def profileYZeroExtension (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  if 0 < r then profileY F r else 0

theorem profileYZeroExtension_match (F : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) : profileYZeroExtension F r = profileY F r := by
  simp [profileYZeroExtension, hr]

/-- The regular-origin factorization makes the right derivative of the
extended slope defect vanish at the origin. -/
theorem profileYZeroExtension_hasDerivAt_zero
    (F H : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hH : ContDiff ℝ 1 H) (hH0 : 0 < H 0)
    (hFactor : ∀ r : ℝ, 0 < r → r < R → F r = r * H (r ^ 2)) :
    HasDerivAt (profileYZeroExtension F) 0 0 := by
  have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs0 : Tendsto (fun r : ℝ => r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hr0.pow 2 using 1
    norm_num
  have hHr : Tendsto (fun r : ℝ => H (r ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (H 0)) := by
    exact hH.continuous.continuousAt.tendsto.comp hs0
  have hHderivr : Tendsto (fun r : ℝ => deriv H (r ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv H 0)) := by
    exact hH.continuous_deriv_one.continuousAt.tendsto.comp hs0
  have hmodel : Tendsto
      (fun r : ℝ => -2 * r * deriv H (r ^ 2) / H (r ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert ((tendsto_const_nhds.mul hr0).mul hHderivr).div
      hHr (ne_of_gt hH0) using 1
    simp
  have hright : Tendsto (slope (profileYZeroExtension F) 0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hmodel.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds,
      hHr.eventually (eventually_gt_nhds hH0)] with r hr hrR hHrpos
    change 0 < r at hr
    have hlocal : F =ᶠ[𝓝 r] (fun t : ℝ => t * H (t ^ 2)) := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show r ∈ Ioo (0 : ℝ) R from ⟨hr, hrR⟩)] with t ht
      exact hFactor t ht.1 ht.2
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
      convert hasDerivAt_pow 2 r using 1
      ring
    have hcomp : HasDerivAt (fun t : ℝ => H (t ^ 2))
        (deriv H (r ^ 2) * (2 * r)) r :=
      (hH.differentiable_one (r ^ 2)).hasDerivAt.comp r hpow
    have hFderiv : deriv F r = H (r ^ 2) +
        2 * r ^ 2 * deriv H (r ^ 2) := by
      rw [hlocal.deriv_eq]
      convert ((hasDerivAt_id r).mul hcomp).deriv using 1
      simp only [id_eq]
      ring
    rw [slope_def_field]
    simp only [profileYZeroExtension, if_pos hr, lt_irrefl, if_false,
      sub_zero, sub_zero, profileY]
    rw [hFactor r hr hrR, hFderiv]
    field_simp [ne_of_gt hr, ne_of_gt hHrpos]
    ring
  have hleft : Tendsto (slope (profileYZeroExtension F) 0)
      (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    have heq : slope (profileYZeroExtension F) 0 =ᶠ[𝓝[<] (0 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [slope_def_field]
      have hnot : ¬ 0 < r := not_lt.mpr hr.le
      simp [profileYZeroExtension, hnot]
    exact tendsto_const_nhds.congr' heq.symm
  exact (hasDerivAt_iff_tendsto_slope_left_right).2 ⟨hleft, hright⟩

/-- The paper's smooth origin factor and positivity of the entire profile
produce the differentiable auxiliary function used in the contact flow. -/
theorem profileYZeroExtension_differentiable
    (F H : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (hH0 : 0 < H 0)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hFactor : ∀ r : ℝ, 0 < r → r < R → F r = r * H (r ^ 2)) :
    Differentiable ℝ (profileYZeroExtension F) := by
  intro r
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have hEq : profileYZeroExtension F =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hr] with t ht
      simp [profileYZeroExtension, not_lt.mpr ht.le]
    exact (differentiableAt_const (𝕜 := ℝ) (0 : ℝ)).congr_of_eventuallyEq hEq
  · subst r
    exact (profileYZeroExtension_hasDerivAt_zero F H R hR hH hH0
      hFactor).differentiableAt
  · have hF' : DifferentiableAt ℝ F r :=
      (hF.of_le (by norm_num)).differentiable_one r
    have hD' : DifferentiableAt ℝ (deriv F) r :=
      (radial_profile_deriv_contDiff_one F hF).differentiable_one r
    have hY' : DifferentiableAt ℝ (profileY F) r := by
      unfold profileY
      exact (((hasDerivAt_id r).mul hD'.hasDerivAt).div
        hF'.hasDerivAt (ne_of_gt (hFpos r hr))).const_sub 1
        |>.differentiableAt
    have hEq : profileYZeroExtension F =ᶠ[𝓝 r] profileY F := by
      filter_upwards [eventually_gt_nhds hr] with t ht
      exact profileYZeroExtension_match F ht
    exact hY'.congr_of_eventuallyEq hEq

/-- An interface ready for the radial-profile theorem: local origin
factorization and the usual whole-space positivity supply, without any
extra analytic hypothesis, the auxiliary `y` and both facts required by
the contact argument. -/
theorem physical_profile_y_extension_from_factor
    (F H : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (hH0 : 0 < H 0)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hFactor : ∀ r : ℝ, 0 < r → r ≤ R → F r = r * H (r ^ 2)) :
    ∃ y : ℝ → ℝ,
      Differentiable ℝ y ∧
        ∀ r : ℝ, 0 < r → y r = profileY F r := by
  refine ⟨profileYZeroExtension F, ?_, ?_⟩
  · exact profileYZeroExtension_differentiable F H R hR hF hH hH0
      hFpos (fun r hr hrR => hFactor r hr hrR.le)
  · intro r hr
    exact profileYZeroExtension_match F hr

/-- The cited radial-profile data, with the auxiliary flow variable and
origin-Taylor remainders removed.  The `C²` factor regularity is a finite
piece of the smooth origin factorization stated in the profile theorem;
`OriginFactorTaylor` constructs the differentiated Peano remainders from it.
The derivative sign of the entire profile is stated in its natural form.
The comparison, contact sign, and ball-energy inequalities are absent. -/
structure PhysicalRadialDataCore (m : ℕ) (R : ℝ) where
  f : ℝ → ℝ
  F : ℝ → ℝ
  Hf : ℝ → ℝ
  HF : ℝ → ℝ
  α : ℝ
  β : ℝ
  hR : 0 < R
  hα : 0 < α
  hβ : 0 < β
  hf0 : f 0 = 0
  hF0 : F 0 = 0
  hHf0 : Hf 0 = β
  hHF0 : HF 0 = α
  hfC2 : ContDiff ℝ 2 f
  hFC2 : ContDiff ℝ 2 F
  hHf : ContDiff ℝ 2 Hf
  hHF : ContDiff ℝ 2 HF
  hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r
  hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1
  hfR : f R = 1
  hFone : Tendsto F atTop (𝓝 (1 : ℝ))
  hFposAll : ∀ r, 0 < r → 0 < F r
  hFltAll : ∀ r, 0 < r → F r < 1
  hFderivPos : ∀ r, 0 < r → 0 < deriv F r
  hFodeAll : ∀ r, 0 < r →
    radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
      (deriv (deriv F) r)
  hfODE : ∀ r, 0 < r → r < R →
    radialODEAt ((m : ℝ) + 3) r
      (f r) (deriv f r) (deriv (deriv f) r)
  hfFactor : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2)
  hFFactor : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2)

/-- The smooth origin factor and the radial equation determine the finite-ball
cubic and quintic coefficients.  Thus they need not be supplied in `Core`. -/
theorem PhysicalRadialDataCore.f_origin_coefficients
    {m : ℕ} {R : ℝ} (p : PhysicalRadialDataCore m R) :
    deriv p.Hf 0 = -(p.Hf 0) / (2 * (((m : ℝ) + 3) + 2)) ∧
      deriv (deriv p.Hf) 0 / 2 =
        (p.Hf 0) ^ 3 / (4 * (((m : ℝ) + 3) + 4)) +
          (p.Hf 0) / (8 * (((m : ℝ) + 3) + 2) * (((m : ℝ) + 3) + 4)) := by
  have hn : (3 : ℝ) ≤ (m : ℝ) + 3 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  apply radial_origin_coefficients_of_local_smooth_factor
    ((m : ℝ) + 3) R p.f p.Hf hn p.hR p.hHf
  · intro r hr hrR
    exact p.hfFactor r hr hrR.le
  · intro r hr hrR
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (p.f r) (deriv p.f r) (deriv (deriv p.f) r) hr).mp
      (p.hfODE r hr hrR)
    exact h

/-- The same coefficient determination for the entire radial profile. -/
theorem PhysicalRadialDataCore.F_origin_coefficients
    {m : ℕ} {R : ℝ} (p : PhysicalRadialDataCore m R) :
    deriv p.HF 0 = -(p.HF 0) / (2 * (((m : ℝ) + 3) + 2)) ∧
      deriv (deriv p.HF) 0 / 2 =
        (p.HF 0) ^ 3 / (4 * (((m : ℝ) + 3) + 4)) +
          (p.HF 0) / (8 * (((m : ℝ) + 3) + 2) * (((m : ℝ) + 3) + 4)) := by
  have hn : (3 : ℝ) ≤ (m : ℝ) + 3 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  apply radial_origin_coefficients_of_local_smooth_factor
    ((m : ℝ) + 3) R p.F p.HF hn p.hR p.hHF
  · intro r hr hrR
    exact p.hFFactor r hr hrR.le
  · intro r hr _
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (p.F r) (deriv p.F r) (deriv (deriv p.F) r) hr).mp
      (p.hFodeAll r hr)
    exact h

/-- Construct the old internal profile package from the cited data.
The auxiliary slope defect and both origin-Taylor interfaces are derived
from smooth factorization rather than supplied as separate inputs. -/
noncomputable def PhysicalRadialDataCore.toPhysicalRadialData
    {m : ℕ} {R : ℝ} (p : PhysicalRadialDataCore m R) :
    PhysicalRadialData m R := by
  let y := profileYZeroExtension p.F
  have hHFpos : 0 < p.HF 0 := by
    rw [p.hHF0]
    exact p.hα
  have hyDiff : Differentiable ℝ y :=
    profileYZeroExtension_differentiable p.F p.HF R p.hR
      p.hFC2 (p.hHF.of_le (by norm_num)) hHFpos p.hFposAll
      (fun r hr hrR => p.hFFactor r hr hrR.le)
  have hfTaylor : RadialOriginTaylorInterior p.f p.β
      (deriv p.Hf 0) (deriv (deriv p.Hf) 0 / 2) R := by
    rw [← p.hHf0]
    exact radialOriginTaylorInterior_of_smooth_factor p.f p.Hf R
      p.hHf (fun r hr hrR => p.hfFactor r hr hrR.le)
  have hFTaylor : RadialOriginTaylorInterior p.F p.α
      (deriv p.HF 0) (deriv (deriv p.HF) 0 / 2) R := by
    rw [← p.hHF0]
    exact radialOriginTaylorInterior_of_smooth_factor p.F p.HF R
      p.hHF (fun r hr hrR => p.hFFactor r hr hrR.le)
  have hyFlt : ∀ r ∈ Ioc (0 : ℝ) R, profileY p.F r < 1 := by
    intro r hr
    have hquot : 0 < r * deriv p.F r / p.F r :=
      div_pos (mul_pos hr.1 (p.hFderivPos r hr.1))
        (p.hFposAll r hr.1)
    unfold profileY
    linarith
  exact {
    f := p.f
    F := p.F
    y := y
    Hf := p.Hf
    HF := p.HF
    α := p.α
    β := p.β
    Af := deriv p.Hf 0
    Bf := deriv (deriv p.Hf) 0 / 2
    AF := deriv p.HF 0
    BF := deriv (deriv p.HF) 0 / 2
    hR := p.hR
    hα := p.hα
    hβ := p.hβ
    hfTaylor := hfTaylor
    hFTaylor := hFTaylor
    hf0 := p.hf0
    hF0 := p.hF0
    hHf0 := p.hHf0
    hHF0 := p.hHF0
    hfC2 := p.hfC2
    hFC2 := p.hFC2
    hHf := p.hHf.of_le (by norm_num)
    hHF := p.hHF.of_le (by norm_num)
    hfpos := p.hfpos
    hflt := p.hflt
    hfR := p.hfR
    hyFlt := hyFlt
    hFone := p.hFone
    hyDiff := hyDiff
    hyMatch := fun r hr => profileYZeroExtension_match p.F hr
    hFposAll := p.hFposAll
    hFltAll := p.hFltAll
    hFodeAll := p.hFodeAll
    hfODE := p.hfODE
    hfFactor := p.hfFactor
    hFFactor := p.hFFactor }

end

end BrezisOP6
