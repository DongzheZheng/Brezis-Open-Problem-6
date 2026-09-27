import BrezisOP6.InfinitySign

/-!
# Far-field candidate residuals

The three barriers in the radial profile expansion are instances of the
single Laurent polynomial `1-a/r²+u/r⁴+v/r⁶`.  This file computes its
actual first and second derivatives and the radial ODE residual.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

def farCandidate (a u v r : ℝ) : ℝ :=
  1 - a * r ^ (-2 : ℤ) +
    u * r ^ (-4 : ℤ) + v * r ^ (-6 : ℤ)

def farCandidateD1 (a u v r : ℝ) : ℝ :=
  2 * a * r ^ (-3 : ℤ) -
    4 * u * r ^ (-5 : ℤ) - 6 * v * r ^ (-7 : ℤ)

def farCandidateD2 (a u v r : ℝ) : ℝ :=
  -6 * a * r ^ (-4 : ℤ) +
    20 * u * r ^ (-6 : ℤ) + 42 * v * r ^ (-8 : ℤ)

def farResidual (n r p p₁ p₂ : ℝ) : ℝ :=
  p₂ + (n - 1) / r * p₁ -
    (n - 1) / r ^ 2 * p + (1 - p ^ 2) * p

/-- The displayed `p'` is the actual derivative of the Laurent barrier. -/
theorem farCandidate_hasDerivAt
    (a u v r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (farCandidate a u v)
      (farCandidateD1 a u v r) r := by
  have h2 := hasDerivAt_zpow (-2 : ℤ) r (Or.inl hr)
  have h4 := hasDerivAt_zpow (-4 : ℤ) r (Or.inl hr)
  have h6 := hasDerivAt_zpow (-6 : ℤ) r (Or.inl hr)
  have hraw :=
    (((hasDerivAt_const r (1 : ℝ)).sub
      ((hasDerivAt_const r a).mul h2)).add
      ((hasDerivAt_const r u).mul h4)).add
      ((hasDerivAt_const r v).mul h6)
  convert hraw using 1
  simp only [farCandidateD1]
  norm_num
  ring

/-- Likewise the displayed `p''` is the derivative of `p'`. -/
theorem farCandidateD1_hasDerivAt
    (a u v r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (farCandidateD1 a u v)
      (farCandidateD2 a u v r) r := by
  have h3 := hasDerivAt_zpow (-3 : ℤ) r (Or.inl hr)
  have h5 := hasDerivAt_zpow (-5 : ℤ) r (Or.inl hr)
  have h7 := hasDerivAt_zpow (-7 : ℤ) r (Or.inl hr)
  have hraw :=
    (((hasDerivAt_const r (2 * a)).mul h3).sub
      ((hasDerivAt_const r (4 * u)).mul h5)).sub
      ((hasDerivAt_const r (6 * v)).mul h7)
  convert hraw using 1
  simp only [farCandidateD2]
  norm_num
  ring

/-- The full residual polynomial in `t=r⁻²`.  Its first three
coefficients control the successive barriers; the remaining terms give
explicit error orders. -/
def farResidualPolynomial (n a u v t : ℝ) : ℝ :=
  (2 * a - n + 1) * t +
  (3 * a * (n - 3) - 3 * a ^ 2 - 2 * u) * t ^ 2 +
  (5 * u * (5 - n) + 6 * a * u + a ^ 3 - 2 * v) * t ^ 3 +
  (7 * v * (7 - n) - 3 * u ^ 2 + 6 * a * v -
    3 * a ^ 2 * u) * t ^ 4 +
  (-6 * u * v - 3 * a ^ 2 * v + 3 * a * u ^ 2) * t ^ 5 +
  (-3 * v ^ 2 - u ^ 3 + 6 * a * u * v) * t ^ 6 +
  (-3 * u ^ 2 * v + 3 * a * v ^ 2) * t ^ 7 -
  3 * u * v ^ 2 * t ^ 8 - v ^ 3 * t ^ 9

/-- Exact ODE residual, with no asymptotic notation. -/
theorem farCandidate_residual_exact
    (n a u v r : ℝ) (hr : r ≠ 0) :
    farResidual n r (farCandidate a u v r)
      (farCandidateD1 a u v r)
      (farCandidateD2 a u v r) =
      farResidualPolynomial n a u v (r ^ (-2 : ℤ)) := by
  unfold farResidual farCandidate farCandidateD1
    farCandidateD2 farResidualPolynomial
  simp only [zpow_neg]
  field_simp [hr]
  ring_nf

/-- The exact residual for `p=1-K/r²`, including both lower-order terms
quoted in the paper. -/
theorem far_p_residual
    (n K r : ℝ) (hr : r ≠ 0) :
    farResidual n r (farCandidate K 0 0 r)
      (farCandidateD1 K 0 0 r)
      (farCandidateD2 K 0 0 r) =
      (2 * K - n + 1) * r ^ (-2 : ℤ) +
      (3 * K * (n - 3) - 3 * K ^ 2) * r ^ (-4 : ℤ) +
      K ^ 3 * r ^ (-6 : ℤ) := by
  rw [farCandidate_residual_exact n K 0 0 r hr]
  unfold farResidualPolynomial
  simp only [zpow_neg]
  field_simp [hr]
  ring_nf

/-- The coefficient of `r⁻⁶` for the fourth-order candidate. -/
def farQ0Tail (n u t : ℝ) : ℝ :=
  let a := ((n - 1) / 2)
  5 * u * (5 - n) + 6 * a * u + a ^ 3 +
  (-3 * u ^ 2 - 3 * a ^ 2 * u) * t +
  3 * a * u ^ 2 * t ^ 2 - u ^ 3 * t ^ 3

/-- For `q₀+u/r⁴`, the leading residual is
`(c_n-2u)r⁻⁴`, where `c_n=3(n-1)(n-5)/4`.
Taking `u=±K` gives both comparison barriers. -/
theorem far_q0_residual_main
    (n u t : ℝ) :
    farResidualPolynomial n ((n - 1) / 2) u 0 t =
      (3 * (n - 1) * (n - 5) / 4 - 2 * u) * t ^ 2 +
      t ^ 3 * farQ0Tail n u t := by
  unfold farResidualPolynomial farQ0Tail
  ring_nf

/-- The dimension-dependent sixth-order residual coefficient `C_n`. -/
def farCoeff6Residual (n : ℝ) : ℝ :=
  -(n - 1) * (5 * n ^ 2 - 94 * n + 329) / 8

def farQ1Tail (n v t : ℝ) : ℝ :=
  let a := (n - 1) / 2
  let u := 3 * (n - 1) * (n - 5) / 8
  7 * v * (7 - n) - 3 * u ^ 2 + 6 * a * v - 3 * a ^ 2 * u +
  (-6 * u * v - 3 * a ^ 2 * v + 3 * a * u ^ 2) * t +
  (-3 * v ^ 2 - u ^ 3 + 6 * a * u * v) * t ^ 2 +
  (-3 * u ^ 2 * v + 3 * a * v ^ 2) * t ^ 3 -
  3 * u * v ^ 2 * t ^ 4 - v ^ 3 * t ^ 5

/-- For `q₁+v/r⁶`, the leading residual is
`(C_n-2v)r⁻⁶`.  Taking `v=±K` gives the third pair of
far-field barriers. -/
theorem far_q1_residual_main
    (n v t : ℝ) :
    farResidualPolynomial n ((n - 1) / 2)
      (3 * (n - 1) * (n - 5) / 8) v t =
      (farCoeff6Residual n - 2 * v) * t ^ 3 +
      t ^ 4 * farQ1Tail n v t := by
  unfold farResidualPolynomial farCoeff6Residual farQ1Tail
  ring_nf

/-- The second derivative test in the exact form used by the half-line
comparison principle. -/
theorem second_deriv_nonneg_at_local_min
    {w : ℝ → ℝ} {c : ℝ}
    (hlocal : IsLocalMin w c)
    (hwDiff : ∀ x, c ≤ x → DifferentiableAt ℝ w x)
    (hderDiff : DifferentiableAt ℝ (deriv w) c) :
    0 ≤ deriv (deriv w) c := by
  by_contra hnot
  have hsecondneg : deriv (deriv w) c < 0 := lt_of_not_ge hnot
  have hfirst : deriv w c = 0 := hlocal.deriv_eq_zero
  have hlim : Filter.Tendsto (slope (deriv w) c)
      (𝓝[>] c) (𝓝 (deriv (deriv w) c)) :=
    hderDiff.hasDerivAt.tendsto_slope.mono_left
      (nhdsGT_le_nhdsNE c)
  have hslopeneg : ∀ᶠ x in 𝓝[>] c,
      slope (deriv w) c x < 0 :=
    hlim.eventually (eventually_lt_nhds hsecondneg)
  have hright : ∀ᶠ x in 𝓝[>] c, c < x :=
    self_mem_nhdsWithin
  have hderivneg : ∀ᶠ x in 𝓝[>] c,
      deriv w x < 0 := by
    filter_upwards [hright, hslopeneg] with x hcx hs
    rw [slope_def_field] at hs
    have hnum : deriv w x - deriv w c < 0 := by
      rcases div_neg_iff.mp hs with h | h
      · linarith [h.2]
      · exact h.1
    simpa only [hfirst, sub_zero] using hnum
  obtain ⟨u, hcu, hu⟩ :=
    (mem_nhdsGT_iff_exists_Ioc_subset.mp hderivneg)
  have hbound : ∀ᶠ x in 𝓝[>] c, x < u :=
    (eventually_lt_nhds hcu).filter_mono nhdsWithin_le_nhds
  have hlocalEvent : ∀ᶠ x in 𝓝[>] c, w c ≤ w x :=
    hlocal.filter_mono nhdsWithin_le_nhds
  obtain ⟨b, hcb, hbu, hwb⟩ :=
    (hright.and (hbound.and hlocalEvent)).exists
  have hanti : StrictAntiOn w (Set.Icc c b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c b)
      (fun x hx => (hwDiff x hx.1).continuousAt.continuousWithinAt)
    intro x hx
    have hxIoo : x ∈ Set.Ioo c b := by simpa using hx
    exact hu ⟨hxIoo.1, le_of_lt (lt_trans hxIoo.2 hbu)⟩
  have hwb_lt : w b < w c :=
    hanti (show c ∈ Set.Icc c b by exact ⟨le_rfl, le_of_lt hcb⟩)
      (show b ∈ Set.Icc c b by exact ⟨le_of_lt hcb, le_rfl⟩)
      hcb
  linarith

/-- A half-line maximum principle in the form needed for radial barrier
comparison.  The local-minimum curvature condition is stated separately;
for a twice differentiable real function it is the elementary second
derivative test. -/
theorem halfLine_nonnegative_of_negative_zeroth
    {w a κ g : ℝ → ℝ} {T : ℝ}
    (hwcont : ContinuousOn w (Set.Ici T))
    (hwT : 0 ≤ w T)
    (hwinfty : Filter.Tendsto w Filter.atTop (𝓝 (0 : ℝ)))
    (hminSecond : ∀ c : ℝ, T < c →
      IsLocalMin w c → 0 ≤ deriv (deriv w) c)
    (hκ : ∀ r : ℝ, T < r → κ r < 0)
    (hg : ∀ r : ℝ, T < r → g r ≤ 0)
    (hode : ∀ r : ℝ, T < r →
      deriv (deriv w) r + a r * deriv w r + κ r * w r = g r) :
    ∀ r : ℝ, T ≤ r → 0 ≤ w r := by
  intro x hx
  by_contra hnot
  have hwx : w x < 0 := lt_of_not_ge hnot
  have hTx : T < x := by
    rcases eq_or_lt_of_le hx with heq | hlt
    · subst x; linarith
    · exact hlt
  have hnear : ∀ᶠ r : ℝ in Filter.atTop, w x < w r :=
    hwinfty.eventually (eventually_gt_nhds hwx)
  obtain ⟨B, hxB, hwB⟩ :=
    ((Filter.eventually_gt_atTop x).and hnear).exists
  have hTB : T < B := lt_trans hTx hxB
  have hxI : x ∈ Set.Icc T B := ⟨hx, le_of_lt hxB⟩
  obtain ⟨c, hcI, hcmin⟩ :=
    isCompact_Icc.exists_isMinOn
      (show (Set.Icc T B).Nonempty from ⟨x, hxI⟩)
      (hwcont.mono (by intro z hz; exact hz.1))
  have hwcle : w c ≤ w x := hcmin hxI
  have hwc : w c < 0 := lt_of_le_of_lt hwcle hwx
  have hTc : T < c := by
    rcases eq_or_lt_of_le hcI.1 with heq | hlt
    · subst c; linarith
    · exact hlt
  have hcB : c < B := by
    rcases eq_or_lt_of_le hcI.2 with heq | hlt
    · subst c; linarith
    · exact hlt
  have hlocal : IsLocalMin w c := by
    filter_upwards [Ioo_mem_nhds hTc hcB] with z hz
    exact hcmin ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hwprime : deriv w c = 0 := hlocal.deriv_eq_zero
  have hwsecond : 0 ≤ deriv (deriv w) c :=
    hminSecond c hTc hlocal
  have hκw : 0 < κ c * w c :=
    mul_pos_of_neg_of_neg (hκ c hTc) hwc
  have hgcle : g c ≤ 0 := hg c hTc
  have hodec := hode c hTc
  rw [hwprime] at hodec
  linarith

/-- The half-line comparison principle with the curvature input discharged
from ordinary `C²` regularity. -/
theorem halfLine_nonnegative_of_negative_zeroth_C2
    {w a κ g : ℝ → ℝ} {T : ℝ}
    (hwDiff : Differentiable ℝ w)
    (hderDiff : ∀ r : ℝ, T < r →
      DifferentiableAt ℝ (deriv w) r)
    (hwT : 0 ≤ w T)
    (hwinfty : Filter.Tendsto w Filter.atTop (𝓝 (0 : ℝ)))
    (hκ : ∀ r : ℝ, T < r → κ r < 0)
    (hg : ∀ r : ℝ, T < r → g r ≤ 0)
    (hode : ∀ r : ℝ, T < r →
      deriv (deriv w) r + a r * deriv w r + κ r * w r = g r) :
    ∀ r : ℝ, T ≤ r → 0 ≤ w r := by
  exact halfLine_nonnegative_of_negative_zeroth
    hwDiff.continuous.continuousOn hwT hwinfty
    (fun c hc hlocal =>
      second_deriv_nonneg_at_local_min hlocal
        (fun x hx => hwDiff x)
        (hderDiff c hc))
    hκ hg hode

/-- Exact difference equation between an ODE profile and a trial barrier.
The cubic nonlinearity factors through `F₀-p₀`, leaving a negative
zeroth-order coefficient when both profiles are close to one. -/
theorem radial_profile_barrier_difference
    (n r F₀ F₁ F₂ p₀ p₁ p₂ : ℝ)
    (hr : 0 < r)
    (hF : radialODEAt n r F₀ F₁ F₂) :
    (F₂ - p₂) + (n - 1) / r * (F₁ - p₁) +
      (1 - (n - 1) / r ^ 2 -
        (F₀ ^ 2 + F₀ * p₀ + p₀ ^ 2)) * (F₀ - p₀) =
      -farResidual n r p₀ p₁ p₂ := by
  have hdiv := (radialODEAt_iff_divided n r F₀ F₁ F₂ hr).mp hF
  unfold farResidual
  have hrne : r ≠ 0 := ne_of_gt hr
  field_simp [hrne] at hdiv ⊢
  nlinarith [hdiv]

/-- Applying the half-line comparison to a genuine radial profile and a
Laurent trial barrier.  All derivative identities for the difference are
derived from the smoothness of `F` and the explicit candidate derivatives. -/
theorem farCandidate_below_profile
    {F : ℝ → ℝ} {n a u v T : ℝ}
    (hT : 0 < T)
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, T < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, T < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hendpoint : farCandidate a u v T ≤ F T)
    (hinfty : Filter.Tendsto
      (fun r => F r - farCandidate a u v r)
      Filter.atTop (𝓝 (0 : ℝ)))
    (hκ : ∀ r, T < r →
      1 - (n - 1) / r ^ 2 -
        (F r ^ 2 + F r * farCandidate a u v r +
          farCandidate a u v r ^ 2) < 0)
    (hres : ∀ r, T < r →
      0 ≤ farResidual n r (farCandidate a u v r)
        (farCandidateD1 a u v r)
        (farCandidateD2 a u v r)) :
    ∀ r, T ≤ r → farCandidate a u v r ≤ F r := by
  let w : ℝ → ℝ := fun s => F s - farCandidate a u v s
  let acoeff : ℝ → ℝ := fun r => (n - 1) / r
  let κ : ℝ → ℝ := fun r =>
    1 - (n - 1) / r ^ 2 -
      (F r ^ 2 + F r * farCandidate a u v r +
        farCandidate a u v r ^ 2)
  let g : ℝ → ℝ := fun r =>
    -farResidual n r (farCandidate a u v r)
      (farCandidateD1 a u v r) (farCandidateD2 a u v r)
  have hwcont : ContinuousOn w (Set.Ici T) := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hT hr
    exact ((hFdiff r).continuousAt.sub
      (farCandidate_hasDerivAt a u v r (ne_of_gt hrpos)).continuousAt).continuousWithinAt
  have hder₁ : ∀ r, T < r →
      deriv w r = deriv F r - farCandidateD1 a u v r := by
    intro r hr
    exact ((hFdiff r).hasDerivAt.sub
      (farCandidate_hasDerivAt a u v r
        (ne_of_gt (lt_trans hT hr)))).deriv
  have hder₂ : ∀ r, T < r →
      HasDerivAt (deriv w)
        (deriv (deriv F) r - farCandidateD2 a u v r) r := by
    intro r hr
    have hEq : deriv w =ᶠ[𝓝 r]
        (fun s => deriv F s - farCandidateD1 a u v s) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
      exact hder₁ s hs
    exact ((hF2diff r hr).hasDerivAt.sub
      (farCandidateD1_hasDerivAt a u v r
        (ne_of_gt (lt_trans hT hr)))).congr_of_eventuallyEq hEq
  have hnonneg := halfLine_nonnegative_of_negative_zeroth
    (w := w) (a := acoeff) (κ := κ) (g := g) (T := T)
    hwcont (show 0 ≤ w T by dsimp [w]; linarith) hinfty
    (fun c hc hlocal =>
      second_deriv_nonneg_at_local_min hlocal
        (fun x hx =>
          ((hFdiff x).hasDerivAt.sub
            (farCandidate_hasDerivAt a u v x
              (ne_of_gt (lt_trans hT (lt_of_lt_of_le hc hx))))).differentiableAt)
        (hder₂ c hc).differentiableAt)
    (fun r hr => hκ r hr)
    (fun r hr => neg_nonpos.mpr (hres r hr))
    (fun r hr => by
      have hdif := radial_profile_barrier_difference n r
        (F r) (deriv F r) (deriv (deriv F) r)
        (farCandidate a u v r) (farCandidateD1 a u v r)
        (farCandidateD2 a u v r) (lt_trans hT hr)
        (hFode r hr)
      simpa [w, acoeff, κ, g, hder₁ r hr, (hder₂ r hr).deriv]
        using hdif)
  intro r hr
  have h := hnonneg r hr
  dsimp [w] at h
  linarith

/-- The companion upper-barrier comparison. A nonpositive candidate
residual and an ordered finite endpoint put the radial profile below the
candidate throughout the half-line. -/
theorem farCandidate_above_profile
    {F : ℝ → ℝ} {n a u v T : ℝ}
    (hT : 0 < T)
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, T < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, T < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hendpoint : F T ≤ farCandidate a u v T)
    (hinfty : Filter.Tendsto
      (fun r => farCandidate a u v r - F r)
      Filter.atTop (𝓝 (0 : ℝ)))
    (hκ : ∀ r, T < r →
      1 - (n - 1) / r ^ 2 -
        (F r ^ 2 + F r * farCandidate a u v r +
          farCandidate a u v r ^ 2) < 0)
    (hres : ∀ r, T < r →
      farResidual n r (farCandidate a u v r)
        (farCandidateD1 a u v r)
        (farCandidateD2 a u v r) ≤ 0) :
    ∀ r, T ≤ r → F r ≤ farCandidate a u v r := by
  let w : ℝ → ℝ := fun s => farCandidate a u v s - F s
  let acoeff : ℝ → ℝ := fun r => (n - 1) / r
  let κ : ℝ → ℝ := fun r =>
    1 - (n - 1) / r ^ 2 -
      (F r ^ 2 + F r * farCandidate a u v r +
        farCandidate a u v r ^ 2)
  let g : ℝ → ℝ := fun r =>
    farResidual n r (farCandidate a u v r)
      (farCandidateD1 a u v r) (farCandidateD2 a u v r)
  have hwcont : ContinuousOn w (Set.Ici T) := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hT hr
    exact ((farCandidate_hasDerivAt a u v r
      (ne_of_gt hrpos)).continuousAt.sub
        (hFdiff r).continuousAt).continuousWithinAt
  have hder₁ : ∀ r, T < r →
      deriv w r = farCandidateD1 a u v r - deriv F r := by
    intro r hr
    exact ((farCandidate_hasDerivAt a u v r
      (ne_of_gt (lt_trans hT hr))).sub
        (hFdiff r).hasDerivAt).deriv
  have hder₂ : ∀ r, T < r →
      HasDerivAt (deriv w)
        (farCandidateD2 a u v r - deriv (deriv F) r) r := by
    intro r hr
    have hEq : deriv w =ᶠ[𝓝 r]
        (fun s => farCandidateD1 a u v s - deriv F s) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
      exact hder₁ s hs
    exact ((farCandidateD1_hasDerivAt a u v r
        (ne_of_gt (lt_trans hT hr))).sub
      (hF2diff r hr).hasDerivAt).congr_of_eventuallyEq hEq
  have hnonneg := halfLine_nonnegative_of_negative_zeroth
    (w := w) (a := acoeff) (κ := κ) (g := g) (T := T)
    hwcont (show 0 ≤ w T by dsimp [w]; linarith) hinfty
    (fun c hc hlocal =>
      second_deriv_nonneg_at_local_min hlocal
        (fun x hx =>
          ((farCandidate_hasDerivAt a u v x
              (ne_of_gt (lt_trans hT (lt_of_lt_of_le hc hx)))).sub
            (hFdiff x).hasDerivAt).differentiableAt)
        (hder₂ c hc).differentiableAt)
    (fun r hr => hκ r hr)
    (fun r hr => hres r hr)
    (fun r hr => by
      have hdif := radial_profile_barrier_difference n r
        (F r) (deriv F r) (deriv (deriv F) r)
        (farCandidate a u v r) (farCandidateD1 a u v r)
        (farCandidateD2 a u v r) (lt_trans hT hr)
        (hFode r hr)
      dsimp [w, acoeff, κ, g]
      rw [(hder₂ r hr).deriv, hder₁ r hr]
      nlinarith [hdif])
  intro r hr
  have h := hnonneg r hr
  dsimp [w] at h
  linarith

end

end BrezisOP6
