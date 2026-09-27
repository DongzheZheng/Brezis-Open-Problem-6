import BrezisOP6.SlopeBarrier

/-!
# Compact minimum extraction for the initial-slope barrier

The endpoint limits of F/G alone do not force an interior minimum:
the origin expansion supplies a strict descent below its limiting value.
This file does not assume that a minimizing point exists. It constructs one
on a compact interval and records the exact ODE obstruction supplied by
SlopeBarrier.lean.
-/

namespace BrezisOP6

open Filter Set Topology

noncomputable section

/-- Quartic coefficient in the origin expansion of the quotient,
expressed in terms of its limiting value \(L=\alpha\sqrt{n+2}\). -/
def ratioQuarticCoefficient (n L : ℝ) : ℝ :=
  L * ((n + 2) * L ^ 2 - (n + 5)) /
    (4 * (n + 4) * (n + 2) ^ 2)

theorem ratioQuarticCoefficient_neg {n L : ℝ}
    (hn : 3 ≤ n) (hL0 : 0 < L) (hL1 : L ≤ 1) :
    ratioQuarticCoefficient n L < 0 := by
  have hLsq : L ^ 2 ≤ 1 := by nlinarith
  have hn2 : 0 < n + 2 := by linarith
  have hn4 : 0 < n + 4 := by linarith
  have hbracket : (n + 2) * L ^ 2 - (n + 5) < 0 := by
    have hmul : (n + 2) * L ^ 2 ≤ (n + 2) * 1 :=
      mul_le_mul_of_nonneg_left hLsq (le_of_lt hn2)
    linarith
  unfold ratioQuarticCoefficient
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hL0 hbracket) (by positivity)

/-- A negative quartic coefficient in the origin expansion supplies
an actual positive radius with \(Z(r)<L\). -/
theorem exists_origin_descent_of_quartic_limit
    {Z : ℝ → ℝ} {L c₄ : ℝ}
    (hc₄ : c₄ < 0)
    (hexp : Tendsto (fun r => (Z r - L) / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 c₄)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ Z r₀ < L := by
  have hnear : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < r ∧ Z r < L := by
    filter_upwards [self_mem_nhdsWithin,
      hexp.eventually (eventually_lt_nhds hc₄)] with r hr hquot
    have hpow : 0 < r ^ 4 := pow_pos hr 4
    have hnum : Z r - L < 0 := by
      rcases (div_neg_iff).mp hquot with ⟨_, hden⟩ | ⟨hnum, _⟩
      · linarith
      · exact hnum
    exact ⟨hr, by linarith⟩
  exact hnear.exists

/-- A positive continuous profile ratio with a strict descent from its
origin limit and a larger limit at infinity has an interior local minimum
with value below one. This is the compactness step in the initial-slope
argument; the minimizing point is constructed, not postulated. -/
theorem exists_ratio_interior_minimum
    {Z : ℝ → ℝ} {L r₀ : ℝ}
    (hcont : ContinuousOn Z (Ioi 0))
    (hzero : Tendsto Z (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hinfty : Tendsto Z atTop (𝓝 (1 : ℝ)))
    (hr₀ : 0 < r₀) (hdescent : Z r₀ < L)
    (hZr₀1 : Z r₀ < 1)
    (hpositive : ∀ r, 0 < r → 0 < Z r) :
    ∃ c : ℝ, 0 < c ∧ 0 < Z c ∧ Z c < 1 ∧ IsLocalMin Z c := by
  have hnear : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      0 < a ∧ a < r₀ ∧ Z r₀ < Z a := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr₀).filter_mono nhdsWithin_le_nhds,
      hzero.eventually (eventually_gt_nhds hdescent)] with a ha har hZa
    exact ⟨ha, har, hZa⟩
  obtain ⟨a, ha₀, har₀, hZa⟩ := hnear.exists
  have hfar : ∀ᶠ b in atTop, r₀ < b ∧ Z r₀ < Z b := by
    filter_upwards [eventually_gt_atTop r₀,
      hinfty.eventually (eventually_gt_nhds hZr₀1)] with b hrb hZb
    exact ⟨hrb, hZb⟩
  obtain ⟨b, hr₀b, hZb⟩ := hfar.exists
  have hr₀mem : r₀ ∈ Icc a b := ⟨le_of_lt har₀, le_of_lt hr₀b⟩
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha₀ hx.1
  obtain ⟨c, hc, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨r₀, hr₀mem⟩ (hcont.mono hsub)
  have hc_le : Z c ≤ Z r₀ := hmin hr₀mem
  have hac : a < c := by
    by_contra hnot
    have heq : c = a := le_antisymm (le_of_not_gt hnot) hc.1
    rw [heq] at hc_le
    linarith
  have hcb : c < b := by
    by_contra hnot
    have heq : c = b := le_antisymm hc.2 (le_of_not_gt hnot)
    rw [heq] at hc_le
    linarith
  have hc₀ : 0 < c := lt_trans ha₀ hac
  refine ⟨c, hc₀, hpositive c hc₀, ?_, ?_⟩
  · linarith
  · exact hmin.isLocalMin (Icc_mem_nhds hac hcb)

/-- The second derivative at an interior local minimum is nonnegative.
The proof uses the sign of the derivative immediately to the right if
the second derivative were negative, followed by the mean-value theorem
in its strict-antitone form. -/
private theorem second_deriv_nonneg_at_local_min
    {Z : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hcont : ContinuousOn Z (Ioi 0))
    (hmin : IsLocalMin Z c) :
    0 ≤ deriv (deriv Z) c := by
  by_contra hnot
  have hsecond : deriv (deriv Z) c < 0 := lt_of_not_ge hnot
  have hfirst : deriv Z c = 0 := hmin.deriv_eq_zero
  have hsign :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hsecond hfirst
  have hneg : ∀ᶠ x in 𝓝[>] c, deriv Z x < 0 := by
    filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with x hx hcx
    have hsub : c - x < 0 := sub_neg.mpr hcx
    rw [sign_neg hsub] at hx
    exact sign_eq_neg_one_iff.mp hx
  have hminright : ∀ᶠ x in 𝓝[>] c, Z c ≤ Z x :=
    hmin.filter_mono nhdsWithin_le_nhds
  obtain ⟨b, hcb, hsub⟩ :=
    (nhdsGT_basis c).mem_iff.mp (hneg.and hminright)
  let x : ℝ := (c + b) / 2
  have hcx : c < x := by dsimp [x]; linarith
  have hxb : x < b := by dsimp [x]; linarith
  have hcontI : ContinuousOn Z (Icc c x) :=
    hcont.mono (by
      intro z hz
      exact lt_of_lt_of_le hc hz.1)
  have hderivNeg : ∀ z ∈ interior (Icc c x), deriv Z z < 0 := by
    intro z hz
    rw [interior_Icc] at hz
    have hcz : c < z := hz.1
    have hzx : z < x := hz.2
    exact (hsub ⟨hcz, lt_trans hzx hxb⟩).1
  have hanti : StrictAntiOn Z (Icc c x) :=
    strictAntiOn_of_deriv_neg (convex_Icc c x) hcontI hderivNeg
  have hlt : Z x < Z c :=
    hanti ⟨le_rfl, le_of_lt hcx⟩
      ⟨le_of_lt hcx, le_rfl⟩ hcx
  have hge : Z c ≤ Z x := (hsub ⟨hcx, hxb⟩).2
  linarith

/-- The entire-profile candidate reconstructed from its ratio to the
explicit barrier. -/
def slopeProduct (n : ℝ) (Z : ℝ → ℝ) (r : ℝ) : ℝ :=
  slopeBarrier n r * Z r

theorem slopeProduct_deriv {n r : ℝ} {Z : ℝ → ℝ}
    (hn : 3 ≤ n) (hZ : DifferentiableAt ℝ Z r) :
    deriv (slopeProduct n Z) r =
      slopeBarrierPrime n r * Z r +
        slopeBarrier n r * deriv Z r := by
  have hcalc := (slopeBarrier_hasDerivAt (n := n) (r := r) hn).mul hZ.hasDerivAt
  exact hcalc.deriv

theorem slopeProduct_second_deriv {n r : ℝ} {Z : ℝ → ℝ}
    (hn : 3 ≤ n) (hr : 0 < r)
    (hZ : ∀ x, 0 < x → DifferentiableAt ℝ Z x)
    (hZ' : DifferentiableAt ℝ (deriv Z) r) :
    deriv (deriv (slopeProduct n Z)) r =
      slopeBarrierSecond n r * Z r +
        2 * slopeBarrierPrime n r * deriv Z r +
        slopeBarrier n r * deriv (deriv Z) r := by
  have hcalc :=
    ((slopeBarrierPrime_hasDerivAt (n := n) (r := r) hn).mul
      (hZ r hr).hasDerivAt).add
    ((slopeBarrier_hasDerivAt (n := n) (r := r) hn).mul
      hZ'.hasDerivAt)
  have hnear : (deriv (slopeProduct n Z)) =ᶠ[𝓝 r]
      (fun x => slopeBarrierPrime n x * Z x +
        slopeBarrier n x * deriv Z x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact slopeProduct_deriv hn (hZ x hx)
  have hsecond := hcalc.congr_of_eventuallyEq hnear
  have hformula := hsecond.deriv
  convert hformula using 1
  ring

/-- The complete compactness-plus-ODE exclusion for a too-small
origin ratio. The only asymptotic input beyond the two endpoint limits
is the stated quartic expansion from the paper's radial ODE analysis.
No minimizing point is assumed; it is extracted from compactness. -/
theorem initial_ratio_not_lt_one
    {n L : ℝ} {Z : ℝ → ℝ}
    (hn : 3 ≤ n) (hL0 : 0 < L)
    (hcont : ContinuousOn Z (Ioi 0))
    (hZdiff : ∀ x, 0 < x → DifferentiableAt ℝ Z x)
    (hZ2diff : ∀ x, 0 < x → DifferentiableAt ℝ (deriv Z) x)
    (hZpos : ∀ x, 0 < x → 0 < Z x)
    (hzero : Tendsto Z (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hinfty : Tendsto Z atTop (𝓝 (1 : ℝ)))
    (hquartic : Tendsto
      (fun r => (Z r - L) / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (ratioQuarticCoefficient n L)))
    (hODE : ∀ r, 0 < r →
      radialGLResidual n r (slopeProduct n Z r)
        (deriv (slopeProduct n Z) r)
        (deriv (deriv (slopeProduct n Z)) r) = 0) :
    1 < L := by
  by_contra hnot
  have hL1 : L ≤ 1 := le_of_not_gt hnot
  have hc₄ : ratioQuarticCoefficient n L < 0 :=
    ratioQuarticCoefficient_neg hn hL0 hL1
  obtain ⟨r₀, hr₀, hdescent⟩ :=
    exists_origin_descent_of_quartic_limit hc₄ hquartic
  obtain ⟨c, hc, hZc0, hZc1, hmin⟩ :=
    exists_ratio_interior_minimum hcont hzero hinfty hr₀
      hdescent (lt_of_lt_of_le hdescent hL1) hZpos
  have hZ₁ : deriv Z c = 0 := hmin.deriv_eq_zero
  have hZ₂ : 0 ≤ deriv (deriv Z) c :=
    second_deriv_nonneg_at_local_min hc hcont hmin
  have hF₁ := slopeProduct_deriv hn (hZdiff c hc)
  have hF₂ := slopeProduct_second_deriv hn hc hZdiff
    (hZ2diff c hc)
  have hF := hODE c hc
  rw [hF₁, hF₂] at hF
  dsimp [slopeProduct] at hF
  rw [hZ₁] at hF
  simp only [mul_zero, add_zero] at hF
  exact slopeBarrier_no_minimum_below_one hn hc hZc0 hZc1 hZ₂ hF

/-- Translating the strict quotient limit into the paper's strict
initial-slope inequality. -/
theorem initial_slope_square_gt {n α L : ℝ}
    (hn : 3 ≤ n) (hL : L = α * Real.sqrt (n + 2))
    (hstrict : 1 < L) :
    1 / (n + 2) < α ^ 2 := by
  have hDpos : 0 < n + 2 := by linarith
  have hsq : (Real.sqrt (n + 2)) ^ 2 = n + 2 :=
    Real.sq_sqrt (le_of_lt hDpos)
  have hLsq : 1 < L ^ 2 := by nlinarith
  rw [hL, mul_pow, hsq] at hLsq
  exact (div_lt_iff₀ hDpos).2 (by nlinarith)

private theorem slopeBarrier_contDiffOn {n : ℝ} (hn : 3 ≤ n) :
    ContDiffOn ℝ 2 (slopeBarrier n) (Ioi 0) := by
  have hD : ContDiffOn ℝ 2
      (fun r : ℝ => r ^ 2 + n + 2) (Ioi 0) := by fun_prop
  have hDne : ∀ r ∈ Ioi (0 : ℝ), r ^ 2 + n + 2 ≠ 0 := by
    intro r hr
    have hpos : 0 < r ^ 2 + n + 2 := by nlinarith [sq_nonneg r]
    exact ne_of_gt hpos
  have hS := hD.sqrt hDne
  have hSne : ∀ r ∈ Ioi (0 : ℝ),
      Real.sqrt (r ^ 2 + n + 2) ≠ 0 := by
    intro r hr
    exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg r]))
  have hId : ContDiffOn ℝ 2 (fun r : ℝ => r) (Ioi 0) := by fun_prop
  simpa only [slopeBarrier] using hId.div hS hSne

/-- The initial-slope barrier for an actual positive \(C^2\) radial
profile \(F\). The endpoint limits and its quartic origin expansion are
stated explicitly. The interior minimizer, both derivative tests, and
the ODE contradiction are proved within this file. -/
theorem entire_profile_initial_slope_gt
    {n α : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α)
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hFC2 : ContDiffOn ℝ 2 F (Ioi 0))
    (hzero : Tendsto (fun r => F r / slopeBarrier n r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (α * Real.sqrt (n + 2))))
    (hinfty : Tendsto (fun r => F r / slopeBarrier n r)
      atTop (𝓝 (1 : ℝ)))
    (hquartic : Tendsto
      (fun r => ((F r / slopeBarrier n r) -
        α * Real.sqrt (n + 2)) / r ^ 4)
      (𝓝[>] (0 : ℝ))
      (𝓝 (ratioQuarticCoefficient n
        (α * Real.sqrt (n + 2)))))
    (hODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    1 / (n + 2) < α ^ 2 := by
  let Z : ℝ → ℝ := fun r => F r / slopeBarrier n r
  have hGpos (r : ℝ) (hr : 0 < r) : 0 < slopeBarrier n r := by
    unfold slopeBarrier
    have hDpos : 0 < r ^ 2 + n + 2 := by
      nlinarith [sq_nonneg r]
    exact div_pos hr (Real.sqrt_pos.2 hDpos)
  have hZC2 : ContDiffOn ℝ 2 Z (Ioi 0) := by
    dsimp [Z]
    exact hFC2.div (slopeBarrier_contDiffOn hn)
      (fun r hr => ne_of_gt (hGpos r hr))
  have hZcont : ContinuousOn Z (Ioi 0) := hZC2.continuousOn
  have hZdiff : ∀ r, 0 < r → DifferentiableAt ℝ Z r := by
    intro r hr
    exact (hZC2.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt
      (by norm_num)
  have hZ2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv Z) r := by
    intro r hr
    exact ((hZC2.contDiffAt (isOpen_Ioi.mem_nhds hr)).derivWithin
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
      (by norm_num)
  have hZpos : ∀ r, 0 < r → 0 < Z r := by
    intro r hr
    exact div_pos (hFpos r hr) (hGpos r hr)
  have hEqOn : EqOn F (slopeProduct n Z) (Ioi 0) := by
    intro r hr
    dsimp [slopeProduct, Z]
    have hGne : slopeBarrier n r ≠ 0 := ne_of_gt (hGpos r hr)
    field_simp
  have hDerivEqOn : EqOn (deriv F)
      (deriv (slopeProduct n Z)) (Ioi 0) :=
    hEqOn.deriv isOpen_Ioi
  have hSecondEqOn : EqOn (deriv (deriv F))
      (deriv (deriv (slopeProduct n Z))) (Ioi 0) :=
    hDerivEqOn.deriv isOpen_Ioi
  have hODEProduct : ∀ r, 0 < r →
      radialGLResidual n r (slopeProduct n Z r)
        (deriv (slopeProduct n Z) r)
        (deriv (deriv (slopeProduct n Z)) r) = 0 := by
    intro r hr
    rw [← hEqOn hr, ← hDerivEqOn hr, ← hSecondEqOn hr]
    exact hODE r hr
  have hDpos : 0 < n + 2 := by linarith
  have hLpos : 0 < α * Real.sqrt (n + 2) :=
    mul_pos hα (Real.sqrt_pos.2 hDpos)
  have hLstrict : 1 < α * Real.sqrt (n + 2) :=
    initial_ratio_not_lt_one hn hLpos hZcont hZdiff hZ2diff
      hZpos hzero hinfty hquartic hODEProduct
  exact initial_slope_square_gt hn rfl hLstrict

end

end BrezisOP6
