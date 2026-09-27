import BrezisOP6.InfinityBarrier

/-!
# First far-field coefficient from the radial equation

The leading residual of `1-a/r²` changes sign at `a=(n-1)/2`.
An exponentially decaying correction can fix the finite endpoint order
without changing that leading coefficient.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- Inverse square radius tends to zero. -/
theorem invSquare_tendsto_zero :
    Filter.Tendsto (fun r : ℝ => r ^ (-2 : ℤ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have hpow : Filter.Tendsto (fun r : ℝ => r ^ 2)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [zpow_neg] using (tendsto_inv_atTop_zero.comp hpow)

/-- The normalized exact residual of `1-a/r²` has leading coefficient
`2a-n+1`. -/
theorem far_p_scaled_residual_limit (n a : ℝ) :
    Filter.Tendsto
      (fun r : ℝ =>
        r ^ 2 * farResidual n r (farCandidate a 0 0 r)
          (farCandidateD1 a 0 0 r)
          (farCandidateD2 a 0 0 r))
      Filter.atTop (𝓝 (2 * a - n + 1)) := by
  have ht := invSquare_tendsto_zero
  have hpoly : Filter.Tendsto
      (fun r : ℝ => (2 * a - n + 1) +
        (3 * a * (n - 3) - 3 * a ^ 2) * r ^ (-2 : ℤ) +
        a ^ 3 * (r ^ (-2 : ℤ)) ^ 2)
      Filter.atTop (𝓝 (2 * a - n + 1)) := by
    convert ((tendsto_const_nhds.add
      (tendsto_const_nhds.mul ht)).add
      (tendsto_const_nhds.mul (ht.pow 2))) using 1
    ext r; ring_nf
  apply hpoly.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [far_p_residual n a r hrne]
  simp only [zpow_neg]
  field_simp [hrne]

/-- Candidate residuals are eventually strictly positive when
`a>(n-1)/2`. -/
theorem far_p_residual_eventually_pos
    {n a : ℝ} (ha : 0 < 2 * a - n + 1) :
    ∀ᶠ r : ℝ in Filter.atTop,
      0 < farResidual n r (farCandidate a 0 0 r)
        (farCandidateD1 a 0 0 r)
        (farCandidateD2 a 0 0 r) := by
  have hscaled : ∀ᶠ r : ℝ in Filter.atTop,
      0 < r ^ 2 * farResidual n r (farCandidate a 0 0 r)
        (farCandidateD1 a 0 0 r)
        (farCandidateD2 a 0 0 r) :=
    (far_p_scaled_residual_limit n a).eventually
      (eventually_gt_nhds ha)
  filter_upwards [hscaled, Filter.eventually_gt_atTop (0 : ℝ)] with r hs hr
  by_contra hnot
  have hres : farResidual n r (farCandidate a 0 0 r)
      (farCandidateD1 a 0 0 r) (farCandidateD2 a 0 0 r) ≤ 0 :=
    le_of_not_gt hnot
  nlinarith [sq_pos_of_pos hr]

/-- Candidate residuals are eventually strictly negative when
`a<(n-1)/2`. -/
theorem far_p_residual_eventually_neg
    {n a : ℝ} (ha : 2 * a - n + 1 < 0) :
    ∀ᶠ r : ℝ in Filter.atTop,
      farResidual n r (farCandidate a 0 0 r)
        (farCandidateD1 a 0 0 r)
        (farCandidateD2 a 0 0 r) < 0 := by
  have hscaled : ∀ᶠ r : ℝ in Filter.atTop,
      r ^ 2 * farResidual n r (farCandidate a 0 0 r)
        (farCandidateD1 a 0 0 r)
        (farCandidateD2 a 0 0 r) < 0 :=
    (far_p_scaled_residual_limit n a).eventually
      (eventually_lt_nhds ha)
  filter_upwards [hscaled, Filter.eventually_gt_atTop (0 : ℝ)] with r hs hr
  by_contra hnot
  have hres : 0 ≤ farResidual n r (farCandidate a 0 0 r)
      (farCandidateD1 a 0 0 r) (farCandidateD2 a 0 0 r) :=
    le_of_not_gt hnot
  nlinarith [sq_pos_of_pos hr]

/-- The endpoint-adjusted first-order candidate.  The sign `s=-1` gives
the lower barrier, while `s=+1` gives the upper barrier. -/
def firstOrderExpBarrier (a c T s r : ℝ) : ℝ :=
  farCandidate a 0 0 r + s * c * Real.exp (T - r)

def firstOrderExpBarrierD1 (a c T s r : ℝ) : ℝ :=
  farCandidateD1 a 0 0 r - s * c * Real.exp (T - r)

def firstOrderExpBarrierD2 (a c T s r : ℝ) : ℝ :=
  farCandidateD2 a 0 0 r + s * c * Real.exp (T - r)

theorem firstOrderExpBarrier_hasDerivAt
    (a c T s r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (firstOrderExpBarrier a c T s)
      (firstOrderExpBarrierD1 a c T s r) r := by
  have hinner : HasDerivAt (fun x : ℝ => T - x) (-1) r := by
    convert (hasDerivAt_const r T).sub (hasDerivAt_id r) using 1
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (T - x))
      (-Real.exp (T - r)) r := by
    convert (Real.hasDerivAt_exp (T - r)).comp r hinner using 1
    ring
  have hraw := (farCandidate_hasDerivAt a 0 0 r hr).add
    ((hasDerivAt_const r (s * c)).mul hexp)
  convert hraw using 1
  simp only [firstOrderExpBarrierD1]
  ring

theorem firstOrderExpBarrierD1_hasDerivAt
    (a c T s r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (firstOrderExpBarrierD1 a c T s)
      (firstOrderExpBarrierD2 a c T s r) r := by
  have hinner : HasDerivAt (fun x : ℝ => T - x) (-1) r := by
    convert (hasDerivAt_const r T).sub (hasDerivAt_id r) using 1
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (T - x))
      (-Real.exp (T - r)) r := by
    convert (Real.hasDerivAt_exp (T - r)).comp r hinner using 1
    ring
  have hraw := (farCandidateD1_hasDerivAt a 0 0 r hr).sub
    ((hasDerivAt_const r (s * c)).mul hexp)
  convert hraw using 1
  simp only [firstOrderExpBarrierD2]
  ring

/-- Exact effect of a correction `h` satisfying `h'=-h`, `h''=h`.
The bracket tends to `-1` when `p,p+h→1` and `r→∞`; hence a negative
correction helps the lower residual and a positive correction helps the
upper residual. -/
theorem farResidual_exp_correction
    (n r p p₁ p₂ h : ℝ) (hr : r ≠ 0) :
    farResidual n r (p + h) (p₁ - h) (p₂ + h) =
      farResidual n r p p₁ p₂ +
        h * (2 - (n - 1) / r - (n - 1) / r ^ 2 -
          (p ^ 2 + p * (p + h) + (p + h) ^ 2)) := by
  unfold farResidual
  field_simp [hr]
  ring

/-- The correction coefficient is strictly negative as soon as both
barrier values lie above `9/10`. -/
theorem exp_correction_bracket_neg
    {n r p q : ℝ}
    (hn : 1 ≤ n) (hr : 0 < r)
    (hp : (9 : ℝ) / 10 ≤ p)
    (hq : (9 : ℝ) / 10 ≤ q) :
    2 - (n - 1) / r - (n - 1) / r ^ 2 -
      (p ^ 2 + p * q + q ^ 2) < 0 := by
  have hpnonneg : 0 ≤ p := by linarith
  have hqnonneg : 0 ≤ q := by linarith
  have hpn : 0 ≤ n - 1 := by linarith
  have hterm1 : 0 ≤ (n - 1) / r := div_nonneg hpn (le_of_lt hr)
  have hterm2 : 0 ≤ (n - 1) / r ^ 2 :=
    div_nonneg hpn (sq_nonneg r)
  have hp2 : (81 : ℝ) / 100 ≤ p ^ 2 := by nlinarith
  have hq2 : (81 : ℝ) / 100 ≤ q ^ 2 := by nlinarith
  have hpq : (81 : ℝ) / 100 ≤ p * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]
  linarith

/-- The exact residual of the endpoint-adjusted candidate. -/
theorem firstOrderExpBarrier_residual
    (n a c T s r : ℝ) (hr : r ≠ 0) :
    farResidual n r (firstOrderExpBarrier a c T s r)
      (firstOrderExpBarrierD1 a c T s r)
      (firstOrderExpBarrierD2 a c T s r) =
      farResidual n r (farCandidate a 0 0 r)
        (farCandidateD1 a 0 0 r) (farCandidateD2 a 0 0 r) +
        s * c * Real.exp (T - r) *
          (2 - (n - 1) / r - (n - 1) / r ^ 2 -
            (farCandidate a 0 0 r ^ 2 +
             farCandidate a 0 0 r * firstOrderExpBarrier a c T s r +
             firstOrderExpBarrier a c T s r ^ 2)) := by
  simpa only [firstOrderExpBarrier, firstOrderExpBarrierD1,
    firstOrderExpBarrierD2] using
    farResidual_exp_correction n r
      (farCandidate a 0 0 r) (farCandidateD1 a 0 0 r)
      (farCandidateD2 a 0 0 r) (s * c * Real.exp (T - r)) hr

/-- A nonnegative endpoint correction preserves the strict lower
residual sign uniformly throughout any half-line on which the two
candidate values stay above `9/10`. -/
theorem lower_exp_residual_pos
    {n a c T r : ℝ}
    (hn : 1 ≤ n) (hr : 0 < r) (hc : 0 ≤ c)
    (hbase : 0 < farResidual n r (farCandidate a 0 0 r)
      (farCandidateD1 a 0 0 r) (farCandidateD2 a 0 0 r))
    (hp : (9 : ℝ) / 10 ≤ farCandidate a 0 0 r)
    (hq : (9 : ℝ) / 10 ≤ firstOrderExpBarrier a c T (-1) r) :
    0 < farResidual n r (firstOrderExpBarrier a c T (-1) r)
      (firstOrderExpBarrierD1 a c T (-1) r)
      (firstOrderExpBarrierD2 a c T (-1) r) := by
  rw [firstOrderExpBarrier_residual n a c T (-1) r (ne_of_gt hr)]
  have hbr := exp_correction_bracket_neg hn hr hp hq
  have hcor : 0 ≤ (-1 : ℝ) * c * Real.exp (T - r) *
      (2 - (n - 1) / r - (n - 1) / r ^ 2 -
        (farCandidate a 0 0 r ^ 2 +
         farCandidate a 0 0 r * firstOrderExpBarrier a c T (-1) r +
         firstOrderExpBarrier a c T (-1) r ^ 2)) := by
    have hneg : (-1 : ℝ) * c * Real.exp (T - r) ≤ 0 := by
      have hexp := Real.exp_pos (T - r)
      nlinarith
    exact mul_nonneg_of_nonpos_of_nonpos hneg (le_of_lt hbr)
  linarith

/-- The corresponding upper residual is strictly negative. -/
theorem upper_exp_residual_neg
    {n a c T r : ℝ}
    (hn : 1 ≤ n) (hr : 0 < r) (hc : 0 ≤ c)
    (hbase : farResidual n r (farCandidate a 0 0 r)
      (farCandidateD1 a 0 0 r) (farCandidateD2 a 0 0 r) < 0)
    (hp : (9 : ℝ) / 10 ≤ farCandidate a 0 0 r)
    (hq : (9 : ℝ) / 10 ≤ firstOrderExpBarrier a c T 1 r) :
    farResidual n r (firstOrderExpBarrier a c T 1 r)
      (firstOrderExpBarrierD1 a c T 1 r)
      (firstOrderExpBarrierD2 a c T 1 r) < 0 := by
  rw [firstOrderExpBarrier_residual n a c T 1 r (ne_of_gt hr)]
  have hbr := exp_correction_bracket_neg hn hr hp hq
  have hcor : c * Real.exp (T - r) *
      (2 - (n - 1) / r - (n - 1) / r ^ 2 -
        (farCandidate a 0 0 r ^ 2 +
         farCandidate a 0 0 r * firstOrderExpBarrier a c T 1 r +
         firstOrderExpBarrier a c T 1 r ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hc (le_of_lt (Real.exp_pos (T - r))))
      (le_of_lt hbr)
  nlinarith

/-- Signed half-line comparison for a general smooth trial profile.
`s=1` places `P` below `F`, while `s=-1` places it above.  The local
derivative identities and the difference ODE are derived inside the proof. -/
theorem radial_profile_trial_comparison
    {F P P₁ P₂ : ℝ → ℝ} {n T s : ℝ}
    (hT : 0 < T)
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, T < r → DifferentiableAt ℝ (deriv F) r)
    (hPder : ∀ r, T ≤ r → HasDerivAt P (P₁ r) r)
    (hP₁der : ∀ r, T < r → HasDerivAt P₁ (P₂ r) r)
    (hFode : ∀ r, T < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hendpoint : 0 ≤ s * (F T - P T))
    (hinfty : Filter.Tendsto (fun r => s * (F r - P r))
      Filter.atTop (𝓝 (0 : ℝ)))
    (hκ : ∀ r, T < r →
      1 - (n - 1) / r ^ 2 -
        (F r ^ 2 + F r * P r + P r ^ 2) < 0)
    (hres : ∀ r, T < r →
      0 ≤ s * farResidual n r (P r) (P₁ r) (P₂ r)) :
    ∀ r, T ≤ r → 0 ≤ s * (F r - P r) := by
  let w : ℝ → ℝ := fun r => s * (F r - P r)
  let acoeff : ℝ → ℝ := fun r => (n - 1) / r
  let κ : ℝ → ℝ := fun r =>
    1 - (n - 1) / r ^ 2 -
      (F r ^ 2 + F r * P r + P r ^ 2)
  let g : ℝ → ℝ := fun r =>
    -s * farResidual n r (P r) (P₁ r) (P₂ r)
  have hwcont : ContinuousOn w (Set.Ici T) := by
    intro r hr
    exact (continuousAt_const.mul
      ((hFdiff r).continuousAt.sub
        (hPder r hr).continuousAt)).continuousWithinAt
  have hder₁ : ∀ r, T < r →
      deriv w r = s * (deriv F r - P₁ r) := by
    intro r hr
    exact (((hFdiff r).hasDerivAt.sub
      (hPder r (le_of_lt hr))).const_mul s).deriv
  have hder₂ : ∀ r, T < r →
      HasDerivAt (deriv w)
        (s * (deriv (deriv F) r - P₂ r)) r := by
    intro r hr
    have hEq : deriv w =ᶠ[𝓝 r]
        (fun x => s * (deriv F x - P₁ x)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
      exact hder₁ x hx
    exact (((hF2diff r hr).hasDerivAt.sub
      (hP₁der r hr)).const_mul s).congr_of_eventuallyEq hEq
  have hnonneg := halfLine_nonnegative_of_negative_zeroth
    (w := w) (a := acoeff) (κ := κ) (g := g) (T := T)
    hwcont (show 0 ≤ w T by exact hendpoint) hinfty
    (fun c hc hlocal =>
      second_deriv_nonneg_at_local_min hlocal
        (fun x hx =>
          (((hFdiff x).hasDerivAt.sub
            (hPder x (le_of_lt (lt_of_lt_of_le hc hx)))).const_mul s).differentiableAt)
        (hder₂ c hc).differentiableAt)
    (fun r hr => hκ r hr)
    (fun r hr => by dsimp [g]; nlinarith [hres r hr])
    (fun r hr => by
      have hdif := radial_profile_barrier_difference n r
        (F r) (deriv F r) (deriv (deriv F) r)
        (P r) (P₁ r) (P₂ r) (lt_trans hT hr)
        (hFode r hr)
      dsimp [w, acoeff, κ, g]
      rw [(hder₂ r hr).deriv, hder₁ r hr]
      linear_combination s * hdif)
  intro r hr
  exact hnonneg r hr

theorem profile_trial_kappa_neg
    {n r F₀ p₀ : ℝ}
    (hn : 1 ≤ n) (_hr : 0 < r)
    (hF : (9 : ℝ) / 10 ≤ F₀)
    (hp : (9 : ℝ) / 10 ≤ p₀) :
    1 - (n - 1) / r ^ 2 -
      (F₀ ^ 2 + F₀ * p₀ + p₀ ^ 2) < 0 := by
  have hterm : 0 ≤ (n - 1) / r ^ 2 := by
    apply div_nonneg
    · linarith
    · exact sq_nonneg r
  have hF2 : (81 : ℝ) / 100 ≤ F₀ ^ 2 := by nlinarith
  have hp2 : (81 : ℝ) / 100 ≤ p₀ ^ 2 := by nlinarith
  have hFp : (81 : ℝ) / 100 ≤ F₀ * p₀ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hF) (sub_nonneg.mpr hp)]
  linarith

/-- Fully instantiated lower comparison for the exponentially corrected
first-order candidate. All derivative and residual hypotheses are obtained
from the earlier algebraic theorems; only the quantitative far-field
closeness and endpoint data remain as inputs. -/
theorem lower_exp_barrier_below_profile
    {F : ℝ → ℝ} {n a c T : ℝ}
    (hT : 0 < T) (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, T < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, T < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hendpoint : firstOrderExpBarrier a c T (-1) T ≤ F T)
    (hinfty : Filter.Tendsto
      (fun r => F r - firstOrderExpBarrier a c T (-1) r)
      Filter.atTop (𝓝 (0 : ℝ)))
    (hFnear : ∀ r, T < r → (9 : ℝ) / 10 ≤ F r)
    (hbaseNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ farCandidate a 0 0 r)
    (htrialNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ firstOrderExpBarrier a c T (-1) r)
    (hbaseRes : ∀ r, T < r →
      0 < farResidual n r (farCandidate a 0 0 r)
        (farCandidateD1 a 0 0 r) (farCandidateD2 a 0 0 r)) :
    ∀ r, T ≤ r → firstOrderExpBarrier a c T (-1) r ≤ F r := by
  have hcomp := radial_profile_trial_comparison
    (F := F) (P := firstOrderExpBarrier a c T (-1))
    (P₁ := firstOrderExpBarrierD1 a c T (-1))
    (P₂ := firstOrderExpBarrierD2 a c T (-1))
    (n := n) (T := T) (s := 1)
    hT hFdiff hF2diff
    (fun r hr => firstOrderExpBarrier_hasDerivAt a c T (-1) r
      (ne_of_gt (lt_of_lt_of_le hT hr)))
    (fun r hr => firstOrderExpBarrierD1_hasDerivAt a c T (-1) r
      (ne_of_gt (lt_trans hT hr)))
    hFode (by simpa using sub_nonneg.mpr hendpoint)
    (by simpa using hinfty)
    (fun r hr => profile_trial_kappa_neg hn (lt_trans hT hr)
      (hFnear r hr) (htrialNear r hr))
    (fun r hr => by
      simpa using le_of_lt (lower_exp_residual_pos hn
        (lt_trans hT hr) hc (hbaseRes r hr)
        (hbaseNear r hr) (htrialNear r hr)))
  intro r hr
  have h := hcomp r hr
  linarith

/-- Upper comparison with the opposite endpoint correction. -/
theorem upper_exp_barrier_above_profile
    {F : ℝ → ℝ} {n a c T : ℝ}
    (hT : 0 < T) (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, T < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, T < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hendpoint : F T ≤ firstOrderExpBarrier a c T 1 T)
    (hinfty : Filter.Tendsto
      (fun r => firstOrderExpBarrier a c T 1 r - F r)
      Filter.atTop (𝓝 (0 : ℝ)))
    (hFnear : ∀ r, T < r → (9 : ℝ) / 10 ≤ F r)
    (hbaseNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ farCandidate a 0 0 r)
    (htrialNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ firstOrderExpBarrier a c T 1 r)
    (hbaseRes : ∀ r, T < r →
      farResidual n r (farCandidate a 0 0 r)
        (farCandidateD1 a 0 0 r) (farCandidateD2 a 0 0 r) < 0) :
    ∀ r, T ≤ r → F r ≤ firstOrderExpBarrier a c T 1 r := by
  have hcomp := radial_profile_trial_comparison
    (F := F) (P := firstOrderExpBarrier a c T 1)
    (P₁ := firstOrderExpBarrierD1 a c T 1)
    (P₂ := firstOrderExpBarrierD2 a c T 1)
    (n := n) (T := T) (s := -1)
    hT hFdiff hF2diff
    (fun r hr => firstOrderExpBarrier_hasDerivAt a c T 1 r
      (ne_of_gt (lt_of_lt_of_le hT hr)))
    (fun r hr => firstOrderExpBarrierD1_hasDerivAt a c T 1 r
      (ne_of_gt (lt_trans hT hr)))
    hFode (by nlinarith [hendpoint])
    (by convert hinfty using 1; ext r; ring)
    (fun r hr => profile_trial_kappa_neg hn (lt_trans hT hr)
      (hFnear r hr) (htrialNear r hr))
    (fun r hr => by
      have hres := upper_exp_residual_neg hn
        (lt_trans hT hr) hc (hbaseRes r hr)
        (hbaseNear r hr) (htrialNear r hr)
      nlinarith)
  intro r hr
  have h := hcomp r hr
  nlinarith

/-- Every fixed inverse-square Laurent candidate tends to one. -/
theorem far_p_tendsto_one (a : ℝ) :
    Filter.Tendsto (farCandidate a 0 0)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_const_nhds (x := a)).mul invSquare_tendsto_zero)
  convert h using 1
  · ext r; simp [farCandidate]
  · ring_nf

/-- Exponential endpoint corrections decay on the half-line. -/
theorem expShift_tendsto_zero (T : ℝ) :
    Filter.Tendsto (fun r : ℝ => Real.exp (T - r))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_const_nhds (x := Real.exp T)).mul
    Real.tendsto_exp_neg_atTop_nhds_zero
  convert h using 1
  · ext r
    simp only [sub_eq_add_neg, Real.exp_add]
  · ring_nf

/-- The exponential correction vanishes even after multiplication by
the radial scale used to read the first asymptotic coefficient. -/
theorem scaled_expShift_tendsto_zero (T : ℝ) :
    Filter.Tendsto (fun r : ℝ => r ^ 2 * Real.exp (T - r))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_const_nhds (x := Real.exp T)).mul
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2)
  convert h using 1
  · ext r
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  · ring_nf

theorem firstOrderExpBarrier_tendsto_one
    (a c T s : ℝ) :
    Filter.Tendsto (firstOrderExpBarrier a c T s)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have h := (far_p_tendsto_one a).add
    ((tendsto_const_nhds (x := s * c)).mul
      (expShift_tendsto_zero T))
  simpa [firstOrderExpBarrier] using h

/-- For each positive coefficient tolerance, the exact radial ODE profile
lies between two first-order candidates corrected at a finite endpoint.
The corrections vanish exponentially and therefore do not alter the
inverse-square coefficients. -/
theorem firstOrder_exp_sandwich
    {F : ℝ → ℝ} {n δ : ℝ}
    (hn : 1 ≤ n) (hδ : 0 < δ)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    ∃ T cLo cHi : ℝ, 0 < T ∧ 0 ≤ cLo ∧ 0 ≤ cHi ∧
      ∀ r : ℝ, T ≤ r →
        firstOrderExpBarrier ((n - 1) / 2 + δ) cLo T (-1) r ≤ F r ∧
        F r ≤ firstOrderExpBarrier ((n - 1) / 2 - δ) cHi T 1 r := by
  let aLo : ℝ := (n - 1) / 2 + δ
  let aHi : ℝ := (n - 1) / 2 - δ
  have hcoefLo : 0 < 2 * aLo - n + 1 := by dsimp [aLo]; linarith
  have hcoefHi : 2 * aHi - n + 1 < 0 := by dsimp [aHi]; linarith
  have hqLo := far_p_tendsto_one aLo
  have hqHi := far_p_tendsto_one aHi
  have hFnearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < F r :=
    hFone.eventually (eventually_gt_nhds (by norm_num))
  have hFnearHi : ∀ᶠ r : ℝ in Filter.atTop,
      F r < (33 : ℝ) / 32 :=
    hFone.eventually (eventually_lt_nhds (by norm_num))
  have hqLonearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < farCandidate aLo 0 0 r :=
    hqLo.eventually (eventually_gt_nhds (by norm_num))
  have hqLonearHi : ∀ᶠ r : ℝ in Filter.atTop,
      farCandidate aLo 0 0 r < (33 : ℝ) / 32 :=
    hqLo.eventually (eventually_lt_nhds (by norm_num))
  have hqHinearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < farCandidate aHi 0 0 r :=
    hqHi.eventually (eventually_gt_nhds (by norm_num))
  have hqHinearHi : ∀ᶠ r : ℝ in Filter.atTop,
      farCandidate aHi 0 0 r < (33 : ℝ) / 32 :=
    hqHi.eventually (eventually_lt_nhds (by norm_num))
  have hresLo := far_p_residual_eventually_pos hcoefLo
  have hresHi := far_p_residual_eventually_neg hcoefHi
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      1 ≤ r ∧
      (31 : ℝ) / 32 < F r ∧ F r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate aLo 0 0 r ∧
      farCandidate aLo 0 0 r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate aHi 0 0 r ∧
      farCandidate aHi 0 0 r < (33 : ℝ) / 32 ∧
      0 < farResidual n r (farCandidate aLo 0 0 r)
        (farCandidateD1 aLo 0 0 r) (farCandidateD2 aLo 0 0 r) ∧
      farResidual n r (farCandidate aHi 0 0 r)
        (farCandidateD1 aHi 0 0 r)
        (farCandidateD2 aHi 0 0 r) < 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      hFnearLo, hFnearHi, hqLonearLo, hqLonearHi,
      hqHinearLo, hqHinearHi, hresLo, hresHi] with
      r hr hFlo hFhi hqLolo hqLohi hqHilo hqHihi hreslo hreshi
    exact ⟨hr, hFlo, hFhi, hqLolo, hqLohi,
      hqHilo, hqHihi, hreslo, hreshi⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
  let T : ℝ := max T₀ 1
  have hTpos : 0 < T := by dsimp [T]; linarith [le_max_right T₀ 1]
  have hTdata : ∀ r, T ≤ r →
      1 ≤ r ∧
      (31 : ℝ) / 32 < F r ∧ F r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate aLo 0 0 r ∧
      farCandidate aLo 0 0 r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate aHi 0 0 r ∧
      farCandidate aHi 0 0 r < (33 : ℝ) / 32 ∧
      0 < farResidual n r (farCandidate aLo 0 0 r)
        (farCandidateD1 aLo 0 0 r) (farCandidateD2 aLo 0 0 r) ∧
      farResidual n r (farCandidate aHi 0 0 r)
        (farCandidateD1 aHi 0 0 r)
        (farCandidateD2 aHi 0 0 r) < 0 := by
    intro r hr
    exact hT₀ r ((le_max_left T₀ 1).trans hr)
  let cLo : ℝ := max 0 (farCandidate aLo 0 0 T - F T)
  let cHi : ℝ := max 0 (F T - farCandidate aHi 0 0 T)
  have hcLo : 0 ≤ cLo := by dsimp [cLo]; exact le_max_left 0 _
  have hcHi : 0 ≤ cHi := by dsimp [cHi]; exact le_max_left 0 _
  have hcLosmall : cLo ≤ (1 : ℝ) / 16 := by
    dsimp [cLo]
    apply max_le (by norm_num)
    have h := hTdata T le_rfl
    linarith [h.2.1, h.2.2.2.1]
  have hcHismall : cHi ≤ (1 : ℝ) / 16 := by
    dsimp [cHi]
    apply max_le (by norm_num)
    have h := hTdata T le_rfl
    linarith [h.2.2.1, h.2.2.2.2.2.1]
  have hExp : ∀ r, T ≤ r → 0 < Real.exp (T - r) ∧
      Real.exp (T - r) ≤ 1 := by
    intro r hr
    exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩
  have htrialLonear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ firstOrderExpBarrier aLo cLo T (-1) r := by
    intro r hr
    have hd := hTdata r (le_of_lt hr)
    have he := hExp r (le_of_lt hr)
    have hprod : cLo * Real.exp (T - r) ≤ cLo := by
      nlinarith [mul_nonneg hcLo (sub_nonneg.mpr he.2)]
    dsimp [firstOrderExpBarrier]
    nlinarith [hd.2.2.2.1, hcLosmall]
  have htrialHinear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ firstOrderExpBarrier aHi cHi T 1 r := by
    intro r hr
    have hd := hTdata r (le_of_lt hr)
    have hprod : 0 ≤ cHi * Real.exp (T - r) :=
      mul_nonneg hcHi (le_of_lt (Real.exp_pos _))
    dsimp [firstOrderExpBarrier]
    nlinarith [hd.2.2.2.2.2.1]
  have hendpointLo : firstOrderExpBarrier aLo cLo T (-1) T ≤ F T := by
    have hc : farCandidate aLo 0 0 T - F T ≤ cLo := by
      dsimp [cLo]; exact le_max_right _ _
    simp only [firstOrderExpBarrier, sub_self, Real.exp_zero, mul_one]
    nlinarith
  have hendpointHi : F T ≤ firstOrderExpBarrier aHi cHi T 1 T := by
    have hc : F T - farCandidate aHi 0 0 T ≤ cHi := by
      dsimp [cHi]; exact le_max_right _ _
    simp only [firstOrderExpBarrier, sub_self, Real.exp_zero, mul_one]
    nlinarith
  have hinftyLo : Filter.Tendsto
      (fun r => F r - firstOrderExpBarrier aLo cLo T (-1) r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert hFone.sub (firstOrderExpBarrier_tendsto_one aLo cLo T (-1)) using 1
    ring_nf
  have hinftyHi : Filter.Tendsto
      (fun r => firstOrderExpBarrier aHi cHi T 1 r - F r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (firstOrderExpBarrier_tendsto_one aHi cHi T 1).sub hFone using 1
    ring_nf
  have hbelow := lower_exp_barrier_below_profile hTpos hn hcLo
    hFdiff (fun r hr => hF2diff r (lt_trans hTpos hr))
    (fun r hr => hFode r (lt_trans hTpos hr))
    hendpointLo hinftyLo
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.1])
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.2.2.1])
    htrialLonear
    (fun r hr => (hTdata r (le_of_lt hr)).2.2.2.2.2.2.2.1)
  have habove := upper_exp_barrier_above_profile hTpos hn hcHi
    hFdiff (fun r hr => hF2diff r (lt_trans hTpos hr))
    (fun r hr => hFode r (lt_trans hTpos hr))
    hendpointHi hinftyHi
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.1])
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.2.2.2.2.1])
    htrialHinear
    (fun r hr => (hTdata r (le_of_lt hr)).2.2.2.2.2.2.2.2)
  refine ⟨T, cLo, cHi, hTpos, hcLo, hcHi, ?_⟩
  intro r hr
  exact ⟨hbelow r hr, habove r hr⟩

/-- Reading the inverse-square coefficient of an adjusted candidate. -/
theorem scaled_firstOrderExpBarrier
    (a c T s r : ℝ) (hr : r ≠ 0) :
    r ^ 2 * (firstOrderExpBarrier a c T s r - 1) =
      -a + s * c * (r ^ 2 * Real.exp (T - r)) := by
  unfold firstOrderExpBarrier farCandidate
  simp only [zpow_neg]
  field_simp [hr]
  ring

/-- The first far-field coefficient follows from `F→1` and the radial
equation, without assuming any profile expansion. -/
theorem radial_profile_first_coefficient
    {F : ℝ → ℝ} {n : ℝ}
    (hn : 1 ≤ n)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-(n - 1) / 2)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨T, cLo, cHi, hTpos, hcLo, hcHi, hsandwich⟩ :=
    firstOrder_exp_sandwich hn hδ hFone hFdiff hF2diff hFode
  have htailLo : Filter.Tendsto
      (fun r : ℝ => cLo * (r ^ 2 * Real.exp (T - r)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := cLo)).mul
      (scaled_expShift_tendsto_zero T) using 1
    ring_nf
  have htailHi : Filter.Tendsto
      (fun r : ℝ => cHi * (r ^ 2 * Real.exp (T - r)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := cHi)).mul
      (scaled_expShift_tendsto_zero T) using 1
    ring_nf
  have hsmallLo : ∀ᶠ r : ℝ in Filter.atTop,
      cLo * (r ^ 2 * Real.exp (T - r)) < ε / 4 :=
    htailLo.eventually (eventually_lt_nhds (by linarith))
  have hsmallHi : ∀ᶠ r : ℝ in Filter.atTop,
      cHi * (r ^ 2 * Real.exp (T - r)) < ε / 4 :=
    htailHi.eventually (eventually_lt_nhds (by linarith))
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      T ≤ r ∧ 0 < r ∧
        cLo * (r ^ 2 * Real.exp (T - r)) < ε / 4 ∧
        cHi * (r ^ 2 * Real.exp (T - r)) < ε / 4 := by
    filter_upwards [Filter.eventually_ge_atTop T,
      Filter.eventually_gt_atTop (0 : ℝ), hsmallLo, hsmallHi] with
      r hr hrpos hlo hhi
    exact ⟨hr, hrpos, hlo, hhi⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro r hrN
  obtain ⟨hrT, hrpos, hsmallLoR, hsmallHiR⟩ := hN r hrN
  have ⟨hlow, hhigh⟩ := hsandwich r hrT
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hlowScaled :
      r ^ 2 *
          (firstOrderExpBarrier ((n - 1) / 2 + δ) cLo T (-1) r - 1) ≤
        r ^ 2 * (F r - 1) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hlow 1) (sq_nonneg r)
  have hhighScaled :
      r ^ 2 * (F r - 1) ≤
        r ^ 2 *
          (firstOrderExpBarrier ((n - 1) / 2 - δ) cHi T 1 r - 1) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hhigh 1) (sq_nonneg r)
  rw [scaled_firstOrderExpBarrier _ _ _ _ r hrne] at hlowScaled hhighScaled
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> dsimp [δ] at * <;> nlinarith

/-- The fourth-order Laurent residual has the expected normalized limit.
This is the algebraic input for the next pair of endpoint-corrected
barriers. -/
theorem far_q0_scaled_residual_limit (n u : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 4 *
        farResidual n r (farCandidate ((n - 1) / 2) u 0 r)
          (farCandidateD1 ((n - 1) / 2) u 0 r)
          (farCandidateD2 ((n - 1) / 2) u 0 r))
      Filter.atTop
      (𝓝 (3 * (n - 1) * (n - 5) / 4 - 2 * u)) := by
  have ht := invSquare_tendsto_zero
  have htailCont : ContinuousAt (farQ0Tail n u) 0 := by
    unfold farQ0Tail
    fun_prop
  have htail := htailCont.tendsto.comp ht
  have hpoly : Filter.Tendsto
      (fun r : ℝ =>
        3 * (n - 1) * (n - 5) / 4 - 2 * u +
          r ^ (-2 : ℤ) * farQ0Tail n u (r ^ (-2 : ℤ)))
      Filter.atTop
      (𝓝 (3 * (n - 1) * (n - 5) / 4 - 2 * u)) := by
    convert (tendsto_const_nhds.add (ht.mul htail)) using 1
    ring_nf
  apply hpoly.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [farCandidate_residual_exact n ((n - 1) / 2) u 0 r hrne]
  rw [far_q0_residual_main n u (r ^ (-2 : ℤ))]
  simp only [zpow_neg]
  field_simp [hrne]

theorem far_q0_residual_eventually_pos
    {n u : ℝ}
    (hu : 0 < 3 * (n - 1) * (n - 5) / 4 - 2 * u) :
    ∀ᶠ r : ℝ in Filter.atTop,
      0 < farResidual n r (farCandidate ((n - 1) / 2) u 0 r)
        (farCandidateD1 ((n - 1) / 2) u 0 r)
        (farCandidateD2 ((n - 1) / 2) u 0 r) := by
  have hscaled :=
    (far_q0_scaled_residual_limit n u).eventually
      (eventually_gt_nhds hu)
  filter_upwards [hscaled, Filter.eventually_gt_atTop (0 : ℝ)] with r hs hr
  by_contra hnot
  have hres : farResidual n r (farCandidate ((n - 1) / 2) u 0 r)
      (farCandidateD1 ((n - 1) / 2) u 0 r)
      (farCandidateD2 ((n - 1) / 2) u 0 r) ≤ 0 := le_of_not_gt hnot
  nlinarith [pow_pos hr 4]

theorem far_q0_residual_eventually_neg
    {n u : ℝ}
    (hu : 3 * (n - 1) * (n - 5) / 4 - 2 * u < 0) :
    ∀ᶠ r : ℝ in Filter.atTop,
      farResidual n r (farCandidate ((n - 1) / 2) u 0 r)
        (farCandidateD1 ((n - 1) / 2) u 0 r)
        (farCandidateD2 ((n - 1) / 2) u 0 r) < 0 := by
  have hscaled :=
    (far_q0_scaled_residual_limit n u).eventually
      (eventually_lt_nhds hu)
  filter_upwards [hscaled, Filter.eventually_gt_atTop (0 : ℝ)] with r hs hr
  by_contra hnot
  have hres : 0 ≤ farResidual n r
      (farCandidate ((n - 1) / 2) u 0 r)
      (farCandidateD1 ((n - 1) / 2) u 0 r)
      (farCandidateD2 ((n - 1) / 2) u 0 r) := le_of_not_gt hnot
  nlinarith [pow_pos hr 4]

def fourthOrderExpBarrier (a u c T s r : ℝ) : ℝ :=
  farCandidate a u 0 r + s * c * Real.exp (T - r)

def fourthOrderExpBarrierD1 (a u c T s r : ℝ) : ℝ :=
  farCandidateD1 a u 0 r - s * c * Real.exp (T - r)

def fourthOrderExpBarrierD2 (a u c T s r : ℝ) : ℝ :=
  farCandidateD2 a u 0 r + s * c * Real.exp (T - r)

theorem fourthOrderExpBarrier_hasDerivAt
    (a u c T s r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fourthOrderExpBarrier a u c T s)
      (fourthOrderExpBarrierD1 a u c T s r) r := by
  have hinner : HasDerivAt (fun x : ℝ => T - x) (-1) r := by
    convert (hasDerivAt_const r T).sub (hasDerivAt_id r) using 1
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (T - x))
      (-Real.exp (T - r)) r := by
    convert (Real.hasDerivAt_exp (T - r)).comp r hinner using 1
    ring
  have hraw := (farCandidate_hasDerivAt a u 0 r hr).add
    ((hasDerivAt_const r (s * c)).mul hexp)
  convert hraw using 1
  simp only [fourthOrderExpBarrierD1]
  ring

theorem fourthOrderExpBarrierD1_hasDerivAt
    (a u c T s r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fourthOrderExpBarrierD1 a u c T s)
      (fourthOrderExpBarrierD2 a u c T s r) r := by
  have hinner : HasDerivAt (fun x : ℝ => T - x) (-1) r := by
    convert (hasDerivAt_const r T).sub (hasDerivAt_id r) using 1
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (T - x))
      (-Real.exp (T - r)) r := by
    convert (Real.hasDerivAt_exp (T - r)).comp r hinner using 1
    ring
  have hraw := (farCandidateD1_hasDerivAt a u 0 r hr).sub
    ((hasDerivAt_const r (s * c)).mul hexp)
  convert hraw using 1
  simp only [fourthOrderExpBarrierD2]
  ring

theorem fourthOrderExpBarrier_residual
    (n a u c T s r : ℝ) (hr : r ≠ 0) :
    farResidual n r (fourthOrderExpBarrier a u c T s r)
      (fourthOrderExpBarrierD1 a u c T s r)
      (fourthOrderExpBarrierD2 a u c T s r) =
      farResidual n r (farCandidate a u 0 r)
        (farCandidateD1 a u 0 r) (farCandidateD2 a u 0 r) +
        s * c * Real.exp (T - r) *
          (2 - (n - 1) / r - (n - 1) / r ^ 2 -
            (farCandidate a u 0 r ^ 2 +
             farCandidate a u 0 r * fourthOrderExpBarrier a u c T s r +
             fourthOrderExpBarrier a u c T s r ^ 2)) := by
  simpa only [fourthOrderExpBarrier, fourthOrderExpBarrierD1,
    fourthOrderExpBarrierD2] using
    farResidual_exp_correction n r
      (farCandidate a u 0 r) (farCandidateD1 a u 0 r)
      (farCandidateD2 a u 0 r) (s * c * Real.exp (T - r)) hr

theorem fourthOrderExpBarrier_tendsto_one (a u c T s : ℝ) :
    Filter.Tendsto (fourthOrderExpBarrier a u c T s)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have hpow4 : Filter.Tendsto (fun r : ℝ => r ^ 4)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)
  have hinv4 : Filter.Tendsto (fun r : ℝ => r ^ (-4 : ℤ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [zpow_neg] using (tendsto_inv_atTop_zero.comp hpow4)
  have hq : Filter.Tendsto (farCandidate a u 0)
      Filter.atTop (𝓝 (1 : ℝ)) := by
    have h := (far_p_tendsto_one a).add
      ((tendsto_const_nhds (x := u)).mul hinv4)
    convert h using 1
    · ext r; simp [farCandidate]
    · ring_nf
  have h := hq.add
    ((tendsto_const_nhds (x := s * c)).mul
      (expShift_tendsto_zero T))
  simpa [fourthOrderExpBarrier] using h

/-- The exponential correction has the favorable sign for either side of
the comparison when its sign is opposite to the signed order parameter. -/
theorem fourthOrder_exp_residual_signed
    {n a u c T s r : ℝ}
    (hn : 1 ≤ n) (hr : 0 < r) (hc : 0 ≤ c)
    (hsq : s ^ 2 = 1)
    (hbase : 0 ≤ s * farResidual n r (farCandidate a u 0 r)
      (farCandidateD1 a u 0 r) (farCandidateD2 a u 0 r))
    (hp : (9 : ℝ) / 10 ≤ farCandidate a u 0 r)
    (hq : (9 : ℝ) / 10 ≤ fourthOrderExpBarrier a u c T (-s) r) :
    0 ≤ s * farResidual n r (fourthOrderExpBarrier a u c T (-s) r)
      (fourthOrderExpBarrierD1 a u c T (-s) r)
      (fourthOrderExpBarrierD2 a u c T (-s) r) := by
  rw [fourthOrderExpBarrier_residual n a u c T (-s) r (ne_of_gt hr)]
  let B : ℝ := 2 - (n - 1) / r - (n - 1) / r ^ 2 -
    (farCandidate a u 0 r ^ 2 +
      farCandidate a u 0 r * fourthOrderExpBarrier a u c T (-s) r +
      fourthOrderExpBarrier a u c T (-s) r ^ 2)
  have hB : B < 0 := exp_correction_bracket_neg hn hr hp hq
  have hcor : 0 ≤ -(c * Real.exp (T - r) * B) := by
    have hpE : 0 ≤ c * Real.exp (T - r) :=
      mul_nonneg hc (le_of_lt (Real.exp_pos _))
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hpE (le_of_lt hB)]
  have hid : s * ((-s) * c * Real.exp (T - r) * B) =
      -(c * Real.exp (T - r) * B) := by
    calc
      _ = -(s ^ 2) * c * Real.exp (T - r) * B := by ring
      _ = _ := by rw [hsq]; ring
  dsimp [B] at hid hcor
  nlinarith [hbase, hcor, hid]

/-- Signed comparison for an exponentially corrected fourth-order
Laurent candidate. -/
theorem fourthOrder_exp_trial_comparison
    {F : ℝ → ℝ} {n a u c T s : ℝ}
    (hT : 0 < T) (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hsq : s ^ 2 = 1)
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, T < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, T < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hendpoint : 0 ≤ s *
      (F T - fourthOrderExpBarrier a u c T (-s) T))
    (hinfty : Filter.Tendsto
      (fun r => s * (F r - fourthOrderExpBarrier a u c T (-s) r))
      Filter.atTop (𝓝 (0 : ℝ)))
    (hFnear : ∀ r, T < r → (9 : ℝ) / 10 ≤ F r)
    (hbaseNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ farCandidate a u 0 r)
    (htrialNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ fourthOrderExpBarrier a u c T (-s) r)
    (hbaseRes : ∀ r, T < r →
      0 ≤ s * farResidual n r (farCandidate a u 0 r)
        (farCandidateD1 a u 0 r) (farCandidateD2 a u 0 r)) :
    ∀ r, T ≤ r → 0 ≤ s *
      (F r - fourthOrderExpBarrier a u c T (-s) r) := by
  exact radial_profile_trial_comparison hT hFdiff hF2diff
    (fun r hr => fourthOrderExpBarrier_hasDerivAt a u c T (-s) r
      (ne_of_gt (lt_of_lt_of_le hT hr)))
    (fun r hr => fourthOrderExpBarrierD1_hasDerivAt a u c T (-s) r
      (ne_of_gt (lt_trans hT hr)))
    hFode hendpoint hinfty
    (fun r hr => profile_trial_kappa_neg hn (lt_trans hT hr)
      (hFnear r hr) (htrialNear r hr))
    (fun r hr => fourthOrder_exp_residual_signed hn
      (lt_trans hT hr) hc hsq (hbaseRes r hr)
      (hbaseNear r hr) (htrialNear r hr))

/-- The fourth-order Laurent candidate tends to one. -/
theorem fourthCandidate_tendsto_one (a u : ℝ) :
    Filter.Tendsto (farCandidate a u 0) Filter.atTop (𝓝 (1 : ℝ)) := by
  convert fourthOrderExpBarrier_tendsto_one a u 0 0 1 using 1
  ext r
  simp [fourthOrderExpBarrier]

/-- Quantitative endpoint-corrected sandwich for the fourth-order term. -/
theorem fourthOrder_exp_sandwich
    {F : ℝ → ℝ} {n δ : ℝ}
    (hn : 1 ≤ n) (hδ : 0 < δ)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    ∃ T cLo cHi : ℝ, 0 < T ∧ 0 ≤ cLo ∧ 0 ≤ cHi ∧
      ∀ r : ℝ, T ≤ r →
        fourthOrderExpBarrier ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8 - δ) cLo T (-1) r ≤ F r ∧
        F r ≤ fourthOrderExpBarrier ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8 + δ) cHi T 1 r := by
  let uLo : ℝ := 3 * (n - 1) * (n - 5) / 8 - δ
  let uHi : ℝ := 3 * (n - 1) * (n - 5) / 8 + δ
  have hcoefLo : 0 < 3 * (n - 1) * (n - 5) / 4 - 2 * uLo := by dsimp [uLo]; linarith
  have hcoefHi : 3 * (n - 1) * (n - 5) / 4 - 2 * uHi < 0 := by dsimp [uHi]; linarith
  have hqLo := fourthCandidate_tendsto_one ((n - 1) / 2) uLo
  have hqHi := fourthCandidate_tendsto_one ((n - 1) / 2) uHi
  have hFnearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < F r :=
    hFone.eventually (eventually_gt_nhds (by norm_num))
  have hFnearHi : ∀ᶠ r : ℝ in Filter.atTop,
      F r < (33 : ℝ) / 32 :=
    hFone.eventually (eventually_lt_nhds (by norm_num))
  have hqLonearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) uLo 0 r :=
    hqLo.eventually (eventually_gt_nhds (by norm_num))
  have hqLonearHi : ∀ᶠ r : ℝ in Filter.atTop,
      farCandidate ((n - 1) / 2) uLo 0 r < (33 : ℝ) / 32 :=
    hqLo.eventually (eventually_lt_nhds (by norm_num))
  have hqHinearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) uHi 0 r :=
    hqHi.eventually (eventually_gt_nhds (by norm_num))
  have hqHinearHi : ∀ᶠ r : ℝ in Filter.atTop,
      farCandidate ((n - 1) / 2) uHi 0 r < (33 : ℝ) / 32 :=
    hqHi.eventually (eventually_lt_nhds (by norm_num))
  have hresLo := far_q0_residual_eventually_pos hcoefLo
  have hresHi := far_q0_residual_eventually_neg hcoefHi
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      1 ≤ r ∧
      (31 : ℝ) / 32 < F r ∧ F r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) uLo 0 r ∧
      farCandidate ((n - 1) / 2) uLo 0 r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) uHi 0 r ∧
      farCandidate ((n - 1) / 2) uHi 0 r < (33 : ℝ) / 32 ∧
      0 < farResidual n r (farCandidate ((n - 1) / 2) uLo 0 r)
        (farCandidateD1 ((n - 1) / 2) uLo 0 r) (farCandidateD2 ((n - 1) / 2) uLo 0 r) ∧
      farResidual n r (farCandidate ((n - 1) / 2) uHi 0 r)
        (farCandidateD1 ((n - 1) / 2) uHi 0 r)
        (farCandidateD2 ((n - 1) / 2) uHi 0 r) < 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      hFnearLo, hFnearHi, hqLonearLo, hqLonearHi,
      hqHinearLo, hqHinearHi, hresLo, hresHi] with
      r hr hFlo hFhi hqLolo hqLohi hqHilo hqHihi hreslo hreshi
    exact ⟨hr, hFlo, hFhi, hqLolo, hqLohi,
      hqHilo, hqHihi, hreslo, hreshi⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
  let T : ℝ := max T₀ 1
  have hTpos : 0 < T := by dsimp [T]; linarith [le_max_right T₀ 1]
  have hTdata : ∀ r, T ≤ r →
      1 ≤ r ∧
      (31 : ℝ) / 32 < F r ∧ F r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) uLo 0 r ∧
      farCandidate ((n - 1) / 2) uLo 0 r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) uHi 0 r ∧
      farCandidate ((n - 1) / 2) uHi 0 r < (33 : ℝ) / 32 ∧
      0 < farResidual n r (farCandidate ((n - 1) / 2) uLo 0 r)
        (farCandidateD1 ((n - 1) / 2) uLo 0 r) (farCandidateD2 ((n - 1) / 2) uLo 0 r) ∧
      farResidual n r (farCandidate ((n - 1) / 2) uHi 0 r)
        (farCandidateD1 ((n - 1) / 2) uHi 0 r)
        (farCandidateD2 ((n - 1) / 2) uHi 0 r) < 0 := by
    intro r hr
    exact hT₀ r ((le_max_left T₀ 1).trans hr)
  let cLo : ℝ := max 0 (farCandidate ((n - 1) / 2) uLo 0 T - F T)
  let cHi : ℝ := max 0 (F T - farCandidate ((n - 1) / 2) uHi 0 T)
  have hcLo : 0 ≤ cLo := by dsimp [cLo]; exact le_max_left 0 _
  have hcHi : 0 ≤ cHi := by dsimp [cHi]; exact le_max_left 0 _
  have hcLosmall : cLo ≤ (1 : ℝ) / 16 := by
    dsimp [cLo]
    apply max_le (by norm_num)
    have h := hTdata T le_rfl
    linarith [h.2.1, h.2.2.2.1]
  have hcHismall : cHi ≤ (1 : ℝ) / 16 := by
    dsimp [cHi]
    apply max_le (by norm_num)
    have h := hTdata T le_rfl
    linarith [h.2.2.1, h.2.2.2.2.2.1]
  have hExp : ∀ r, T ≤ r → 0 < Real.exp (T - r) ∧
      Real.exp (T - r) ≤ 1 := by
    intro r hr
    exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩
  have htrialLonear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ fourthOrderExpBarrier ((n - 1) / 2) uLo cLo T (-1) r := by
    intro r hr
    have hd := hTdata r (le_of_lt hr)
    have he := hExp r (le_of_lt hr)
    have hprod : cLo * Real.exp (T - r) ≤ cLo := by
      nlinarith [mul_nonneg hcLo (sub_nonneg.mpr he.2)]
    dsimp [fourthOrderExpBarrier]
    nlinarith [hd.2.2.2.1, hcLosmall]
  have htrialHinear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ fourthOrderExpBarrier ((n - 1) / 2) uHi cHi T 1 r := by
    intro r hr
    have hd := hTdata r (le_of_lt hr)
    have hprod : 0 ≤ cHi * Real.exp (T - r) :=
      mul_nonneg hcHi (le_of_lt (Real.exp_pos _))
    dsimp [fourthOrderExpBarrier]
    nlinarith [hd.2.2.2.2.2.1]
  have hendpointLo : fourthOrderExpBarrier ((n - 1) / 2) uLo cLo T (-1) T ≤ F T := by
    have hc : farCandidate ((n - 1) / 2) uLo 0 T - F T ≤ cLo := by
      dsimp [cLo]; exact le_max_right _ _
    simp only [fourthOrderExpBarrier, sub_self, Real.exp_zero, mul_one]
    nlinarith
  have hendpointHi : F T ≤ fourthOrderExpBarrier ((n - 1) / 2) uHi cHi T 1 T := by
    have hc : F T - farCandidate ((n - 1) / 2) uHi 0 T ≤ cHi := by
      dsimp [cHi]; exact le_max_right _ _
    simp only [fourthOrderExpBarrier, sub_self, Real.exp_zero, mul_one]
    nlinarith
  have hinftyLo : Filter.Tendsto
      (fun r => F r - fourthOrderExpBarrier ((n - 1) / 2) uLo cLo T (-1) r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert hFone.sub
      (fourthOrderExpBarrier_tendsto_one ((n - 1) / 2) uLo cLo T (-1)) using 1
    ring_nf
  have hinftyHi : Filter.Tendsto
      (fun r => fourthOrderExpBarrier ((n - 1) / 2) uHi cHi T 1 r - F r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (fourthOrderExpBarrier_tendsto_one
      ((n - 1) / 2) uHi cHi T 1).sub hFone using 1
    ring_nf
  have hbelow := fourthOrder_exp_trial_comparison
    (F := F) (n := n) (a := (n - 1) / 2) (u := uLo)
    (c := cLo) (T := T) (s := 1)
    hTpos hn hcLo (by norm_num)
    hFdiff (fun r hr => hF2diff r (lt_trans hTpos hr))
    (fun r hr => hFode r (lt_trans hTpos hr))
    (by simpa using sub_nonneg.mpr hendpointLo)
    (by simpa using hinftyLo)
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.1])
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.2.2.1])
    htrialLonear
    (fun r hr => by
      simpa using le_of_lt
        (hTdata r (le_of_lt hr)).2.2.2.2.2.2.2.1)
  have habove := fourthOrder_exp_trial_comparison
    (F := F) (n := n) (a := (n - 1) / 2) (u := uHi)
    (c := cHi) (T := T) (s := -1)
    hTpos hn hcHi (by norm_num)
    hFdiff (fun r hr => hF2diff r (lt_trans hTpos hr))
    (fun r hr => hFode r (lt_trans hTpos hr))
    (by nlinarith [hendpointHi])
    (by convert hinftyHi using 1; ext r; ring_nf)
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.1])
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.2.2.2.2.1])
    (by simpa only [neg_neg] using htrialHinear)
    (fun r hr => by
      have hres := (hTdata r (le_of_lt hr)).2.2.2.2.2.2.2.2
      nlinarith)
  refine ⟨T, cLo, cHi, hTpos, hcLo, hcHi, ?_⟩
  intro r hr
  constructor
  · have h := hbelow r hr
    linarith
  · have h := habove r hr
    nlinarith

theorem scaled4_expShift_tendsto_zero (T : ℝ) :
    Filter.Tendsto (fun r : ℝ => r ^ 4 * Real.exp (T - r))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_const_nhds (x := Real.exp T)).mul
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4)
  convert h using 1
  · ext r
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  · ring_nf

theorem scaled_fourthOrderExpBarrier
    (a u c T s r : ℝ) (hr : r ≠ 0) :
    r ^ 4 * (fourthOrderExpBarrier a u c T s r - 1 +
      a * r ^ (-2 : ℤ)) =
      u + s * c * (r ^ 4 * Real.exp (T - r)) := by
  unfold fourthOrderExpBarrier farCandidate
  simp only [zpow_neg]
  field_simp [hr]
  ring

/-- The second far-field coefficient follows directly from `F→1` and
the radial equation.  The first coefficient cancels in the scaled
difference; no derivative expansion is asserted here. -/
theorem radial_profile_second_coefficient
    {F : ℝ → ℝ} {n : ℝ}
    (hn : 1 ≤ n)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 4 *
        (F r - 1 + ((n - 1) / 2) * r ^ (-2 : ℤ)))
      Filter.atTop
      (𝓝 (3 * (n - 1) * (n - 5) / 8)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨T, cLo, cHi, hTpos, hcLo, hcHi, hsandwich⟩ :=
    fourthOrder_exp_sandwich hn hδ hFone hFdiff hF2diff hFode
  have htailLo : Filter.Tendsto
      (fun r : ℝ => cLo * (r ^ 4 * Real.exp (T - r)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := cLo)).mul
      (scaled4_expShift_tendsto_zero T) using 1
    ring_nf
  have htailHi : Filter.Tendsto
      (fun r : ℝ => cHi * (r ^ 4 * Real.exp (T - r)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := cHi)).mul
      (scaled4_expShift_tendsto_zero T) using 1
    ring_nf
  have hsmallLo : ∀ᶠ r : ℝ in Filter.atTop,
      cLo * (r ^ 4 * Real.exp (T - r)) < ε / 4 :=
    htailLo.eventually (eventually_lt_nhds (by linarith))
  have hsmallHi : ∀ᶠ r : ℝ in Filter.atTop,
      cHi * (r ^ 4 * Real.exp (T - r)) < ε / 4 :=
    htailHi.eventually (eventually_lt_nhds (by linarith))
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      T ≤ r ∧ 0 < r ∧
        cLo * (r ^ 4 * Real.exp (T - r)) < ε / 4 ∧
        cHi * (r ^ 4 * Real.exp (T - r)) < ε / 4 := by
    filter_upwards [Filter.eventually_ge_atTop T,
      Filter.eventually_gt_atTop (0 : ℝ), hsmallLo, hsmallHi] with
      r hr hrpos hlo hhi
    exact ⟨hr, hrpos, hlo, hhi⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro r hrN
  obtain ⟨hrT, hrpos, hsmallLoR, hsmallHiR⟩ := hN r hrN
  have ⟨hlow, hhigh⟩ := hsandwich r hrT
  have hrne : r ≠ 0 := ne_of_gt hrpos
  let a : ℝ := (n - 1) / 2
  let b : ℝ := 3 * (n - 1) * (n - 5) / 8
  have hlowScaled :
      r ^ 4 *
          (fourthOrderExpBarrier a (b - δ) cLo T (-1) r - 1 +
            a * r ^ (-2 : ℤ)) ≤
        r ^ 4 * (F r - 1 + a * r ^ (-2 : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hlow])
      (le_of_lt (pow_pos hrpos 4))
  have hhighScaled :
      r ^ 4 * (F r - 1 + a * r ^ (-2 : ℤ)) ≤
        r ^ 4 *
          (fourthOrderExpBarrier a (b + δ) cHi T 1 r - 1 +
            a * r ^ (-2 : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hhigh])
      (le_of_lt (pow_pos hrpos 4))
  rw [scaled_fourthOrderExpBarrier _ _ _ _ _ r hrne] at hlowScaled hhighScaled
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> dsimp [a, b, δ] at * <;> nlinarith

/-- The sixth-order Laurent residual has its predicted leading
coefficient. -/
theorem far_q1_scaled_residual_limit (n v : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 6 *
        farResidual n r
          (farCandidate ((n - 1) / 2)
            (3 * (n - 1) * (n - 5) / 8) v r)
          (farCandidateD1 ((n - 1) / 2)
            (3 * (n - 1) * (n - 5) / 8) v r)
          (farCandidateD2 ((n - 1) / 2)
            (3 * (n - 1) * (n - 5) / 8) v r))
      Filter.atTop (𝓝 (farCoeff6Residual n - 2 * v)) := by
  have ht := invSquare_tendsto_zero
  have htailCont : ContinuousAt (farQ1Tail n v) 0 := by
    unfold farQ1Tail
    fun_prop
  have htail := htailCont.tendsto.comp ht
  have hpoly : Filter.Tendsto
      (fun r : ℝ => farCoeff6Residual n - 2 * v +
        r ^ (-2 : ℤ) * farQ1Tail n v (r ^ (-2 : ℤ)))
      Filter.atTop (𝓝 (farCoeff6Residual n - 2 * v)) := by
    convert (tendsto_const_nhds.add (ht.mul htail)) using 1
    ring_nf
  apply hpoly.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [farCandidate_residual_exact n ((n - 1) / 2)
    (3 * (n - 1) * (n - 5) / 8) v r hrne]
  rw [far_q1_residual_main n v (r ^ (-2 : ℤ))]
  simp only [zpow_neg]
  field_simp [hrne]

theorem far_q1_residual_eventually_pos
    {n v : ℝ} (hv : 0 < farCoeff6Residual n - 2 * v) :
    ∀ᶠ r : ℝ in Filter.atTop,
      0 < farResidual n r
        (farCandidate ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8) v r)
        (farCandidateD1 ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8) v r)
        (farCandidateD2 ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8) v r) := by
  have hs := (far_q1_scaled_residual_limit n v).eventually
    (eventually_gt_nhds hv)
  filter_upwards [hs, Filter.eventually_gt_atTop (0 : ℝ)] with r hs hr
  by_contra hnot
  have hres : farResidual n r
      (farCandidate ((n - 1) / 2)
        (3 * (n - 1) * (n - 5) / 8) v r)
      (farCandidateD1 ((n - 1) / 2)
        (3 * (n - 1) * (n - 5) / 8) v r)
      (farCandidateD2 ((n - 1) / 2)
        (3 * (n - 1) * (n - 5) / 8) v r) ≤ 0 := le_of_not_gt hnot
  nlinarith [pow_pos hr 6]

theorem far_q1_residual_eventually_neg
    {n v : ℝ} (hv : farCoeff6Residual n - 2 * v < 0) :
    ∀ᶠ r : ℝ in Filter.atTop,
      farResidual n r
        (farCandidate ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8) v r)
        (farCandidateD1 ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8) v r)
        (farCandidateD2 ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8) v r) < 0 := by
  have hs := (far_q1_scaled_residual_limit n v).eventually
    (eventually_lt_nhds hv)
  filter_upwards [hs, Filter.eventually_gt_atTop (0 : ℝ)] with r hs hr
  by_contra hnot
  have hres : 0 ≤ farResidual n r
      (farCandidate ((n - 1) / 2)
        (3 * (n - 1) * (n - 5) / 8) v r)
      (farCandidateD1 ((n - 1) / 2)
        (3 * (n - 1) * (n - 5) / 8) v r)
      (farCandidateD2 ((n - 1) / 2)
        (3 * (n - 1) * (n - 5) / 8) v r) := le_of_not_gt hnot
  nlinarith [pow_pos hr 6]

def sixthOrderExpBarrier (a u v c T s r : ℝ) : ℝ :=
  farCandidate a u v r + s * c * Real.exp (T - r)

def sixthOrderExpBarrierD1 (a u v c T s r : ℝ) : ℝ :=
  farCandidateD1 a u v r - s * c * Real.exp (T - r)

def sixthOrderExpBarrierD2 (a u v c T s r : ℝ) : ℝ :=
  farCandidateD2 a u v r + s * c * Real.exp (T - r)

theorem sixthOrderExpBarrier_hasDerivAt
    (a u v c T s r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (sixthOrderExpBarrier a u v c T s)
      (sixthOrderExpBarrierD1 a u v c T s r) r := by
  have hinner : HasDerivAt (fun x : ℝ => T - x) (-1) r := by
    convert (hasDerivAt_const r T).sub (hasDerivAt_id r) using 1
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (T - x))
      (-Real.exp (T - r)) r := by
    convert (Real.hasDerivAt_exp (T - r)).comp r hinner using 1
    ring
  have hraw := (farCandidate_hasDerivAt a u v r hr).add
    ((hasDerivAt_const r (s * c)).mul hexp)
  convert hraw using 1
  simp only [sixthOrderExpBarrierD1]
  ring

theorem sixthOrderExpBarrierD1_hasDerivAt
    (a u v c T s r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (sixthOrderExpBarrierD1 a u v c T s)
      (sixthOrderExpBarrierD2 a u v c T s r) r := by
  have hinner : HasDerivAt (fun x : ℝ => T - x) (-1) r := by
    convert (hasDerivAt_const r T).sub (hasDerivAt_id r) using 1
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (T - x))
      (-Real.exp (T - r)) r := by
    convert (Real.hasDerivAt_exp (T - r)).comp r hinner using 1
    ring
  have hraw := (farCandidateD1_hasDerivAt a u v r hr).sub
    ((hasDerivAt_const r (s * c)).mul hexp)
  convert hraw using 1
  simp only [sixthOrderExpBarrierD2]
  ring

theorem sixthOrderExpBarrier_residual
    (n a u v c T s r : ℝ) (hr : r ≠ 0) :
    farResidual n r (sixthOrderExpBarrier a u v c T s r)
      (sixthOrderExpBarrierD1 a u v c T s r)
      (sixthOrderExpBarrierD2 a u v c T s r) =
      farResidual n r (farCandidate a u v r)
        (farCandidateD1 a u v r) (farCandidateD2 a u v r) +
        s * c * Real.exp (T - r) *
          (2 - (n - 1) / r - (n - 1) / r ^ 2 -
            (farCandidate a u v r ^ 2 +
             farCandidate a u v r * sixthOrderExpBarrier a u v c T s r +
             sixthOrderExpBarrier a u v c T s r ^ 2)) := by
  simpa only [sixthOrderExpBarrier, sixthOrderExpBarrierD1,
    sixthOrderExpBarrierD2] using
    farResidual_exp_correction n r
      (farCandidate a u v r) (farCandidateD1 a u v r)
      (farCandidateD2 a u v r) (s * c * Real.exp (T - r)) hr

theorem sixthOrderExpBarrier_tendsto_one (a u v c T s : ℝ) :
    Filter.Tendsto (sixthOrderExpBarrier a u v c T s)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have hpow6 : Filter.Tendsto (fun r : ℝ => r ^ 6)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)
  have hinv6 : Filter.Tendsto (fun r : ℝ => r ^ (-6 : ℤ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [zpow_neg] using (tendsto_inv_atTop_zero.comp hpow6)
  have hq : Filter.Tendsto (farCandidate a u v)
      Filter.atTop (𝓝 (1 : ℝ)) := by
    have h := (fourthCandidate_tendsto_one a u).add
      ((tendsto_const_nhds (x := v)).mul hinv6)
    convert h using 1
    · ext r; simp [farCandidate]
    · ring_nf
  have h := hq.add
    ((tendsto_const_nhds (x := s * c)).mul
      (expShift_tendsto_zero T))
  simpa [sixthOrderExpBarrier] using h

/-- The exponential correction has the favorable sign for either side of
the comparison when its sign is opposite to the signed order parameter. -/
theorem sixthOrder_exp_residual_signed
    {n a u v c T s r : ℝ}
    (hn : 1 ≤ n) (hr : 0 < r) (hc : 0 ≤ c)
    (hsq : s ^ 2 = 1)
    (hbase : 0 ≤ s * farResidual n r (farCandidate a u v r)
      (farCandidateD1 a u v r) (farCandidateD2 a u v r))
    (hp : (9 : ℝ) / 10 ≤ farCandidate a u v r)
    (hq : (9 : ℝ) / 10 ≤ sixthOrderExpBarrier a u v c T (-s) r) :
    0 ≤ s * farResidual n r (sixthOrderExpBarrier a u v c T (-s) r)
      (sixthOrderExpBarrierD1 a u v c T (-s) r)
      (sixthOrderExpBarrierD2 a u v c T (-s) r) := by
  rw [sixthOrderExpBarrier_residual n a u v c T (-s) r (ne_of_gt hr)]
  let B : ℝ := 2 - (n - 1) / r - (n - 1) / r ^ 2 -
    (farCandidate a u v r ^ 2 +
      farCandidate a u v r * sixthOrderExpBarrier a u v c T (-s) r +
      sixthOrderExpBarrier a u v c T (-s) r ^ 2)
  have hB : B < 0 := exp_correction_bracket_neg hn hr hp hq
  have hcor : 0 ≤ -(c * Real.exp (T - r) * B) := by
    have hpE : 0 ≤ c * Real.exp (T - r) :=
      mul_nonneg hc (le_of_lt (Real.exp_pos _))
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hpE (le_of_lt hB)]
  have hid : s * ((-s) * c * Real.exp (T - r) * B) =
      -(c * Real.exp (T - r) * B) := by
    calc
      _ = -(s ^ 2) * c * Real.exp (T - r) * B := by ring
      _ = _ := by rw [hsq]; ring
  dsimp [B] at hid hcor
  nlinarith [hbase, hcor, hid]

/-- Signed comparison for an exponentially corrected fourth-order
Laurent candidate. -/
theorem sixthOrder_exp_trial_comparison
    {F : ℝ → ℝ} {n a u v c T s : ℝ}
    (hT : 0 < T) (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hsq : s ^ 2 = 1)
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, T < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, T < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hendpoint : 0 ≤ s *
      (F T - sixthOrderExpBarrier a u v c T (-s) T))
    (hinfty : Filter.Tendsto
      (fun r => s * (F r - sixthOrderExpBarrier a u v c T (-s) r))
      Filter.atTop (𝓝 (0 : ℝ)))
    (hFnear : ∀ r, T < r → (9 : ℝ) / 10 ≤ F r)
    (hbaseNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ farCandidate a u v r)
    (htrialNear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ sixthOrderExpBarrier a u v c T (-s) r)
    (hbaseRes : ∀ r, T < r →
      0 ≤ s * farResidual n r (farCandidate a u v r)
        (farCandidateD1 a u v r) (farCandidateD2 a u v r)) :
    ∀ r, T ≤ r → 0 ≤ s *
      (F r - sixthOrderExpBarrier a u v c T (-s) r) := by
  exact radial_profile_trial_comparison hT hFdiff hF2diff
    (fun r hr => sixthOrderExpBarrier_hasDerivAt a u v c T (-s) r
      (ne_of_gt (lt_of_lt_of_le hT hr)))
    (fun r hr => sixthOrderExpBarrierD1_hasDerivAt a u v c T (-s) r
      (ne_of_gt (lt_trans hT hr)))
    hFode hendpoint hinfty
    (fun r hr => profile_trial_kappa_neg hn (lt_trans hT hr)
      (hFnear r hr) (htrialNear r hr))
    (fun r hr => sixthOrder_exp_residual_signed hn
      (lt_trans hT hr) hc hsq (hbaseRes r hr)
      (hbaseNear r hr) (htrialNear r hr))


theorem sixthCandidate_tendsto_one (a u v : ℝ) :
    Filter.Tendsto (farCandidate a u v) Filter.atTop (𝓝 (1 : ℝ)) := by
  convert sixthOrderExpBarrier_tendsto_one a u v 0 0 1 using 1
  ext r
  simp [sixthOrderExpBarrier]

theorem sixthOrder_exp_sandwich
    {F : ℝ → ℝ} {n δ : ℝ}
    (hn : 1 ≤ n) (hδ : 0 < δ)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    ∃ T cLo cHi : ℝ, 0 < T ∧ 0 ≤ cLo ∧ 0 ≤ cHi ∧
      ∀ r : ℝ, T ≤ r →
        sixthOrderExpBarrier ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8)
          (farCoeff6Residual n / 2 - δ) cLo T (-1) r ≤ F r ∧
        F r ≤ sixthOrderExpBarrier ((n - 1) / 2)
          (3 * (n - 1) * (n - 5) / 8)
          (farCoeff6Residual n / 2 + δ) cHi T 1 r := by
  let vLo : ℝ := farCoeff6Residual n / 2 - δ
  let vHi : ℝ := farCoeff6Residual n / 2 + δ
  have hcoefLo : 0 < farCoeff6Residual n - 2 * vLo := by dsimp [vLo]; linarith
  have hcoefHi : farCoeff6Residual n - 2 * vHi < 0 := by dsimp [vHi]; linarith
  have hqLo := sixthCandidate_tendsto_one ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo
  have hqHi := sixthCandidate_tendsto_one ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi
  have hFnearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < F r :=
    hFone.eventually (eventually_gt_nhds (by norm_num))
  have hFnearHi : ∀ᶠ r : ℝ in Filter.atTop,
      F r < (33 : ℝ) / 32 :=
    hFone.eventually (eventually_lt_nhds (by norm_num))
  have hqLonearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r :=
    hqLo.eventually (eventually_gt_nhds (by norm_num))
  have hqLonearHi : ∀ᶠ r : ℝ in Filter.atTop,
      farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r < (33 : ℝ) / 32 :=
    hqLo.eventually (eventually_lt_nhds (by norm_num))
  have hqHinearLo : ∀ᶠ r : ℝ in Filter.atTop,
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r :=
    hqHi.eventually (eventually_gt_nhds (by norm_num))
  have hqHinearHi : ∀ᶠ r : ℝ in Filter.atTop,
      farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r < (33 : ℝ) / 32 :=
    hqHi.eventually (eventually_lt_nhds (by norm_num))
  have hresLo := far_q1_residual_eventually_pos hcoefLo
  have hresHi := far_q1_residual_eventually_neg hcoefHi
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      1 ≤ r ∧
      (31 : ℝ) / 32 < F r ∧ F r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r ∧
      farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r ∧
      farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r < (33 : ℝ) / 32 ∧
      0 < farResidual n r (farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r)
        (farCandidateD1 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r) (farCandidateD2 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r) ∧
      farResidual n r (farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r)
        (farCandidateD1 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r)
        (farCandidateD2 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r) < 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      hFnearLo, hFnearHi, hqLonearLo, hqLonearHi,
      hqHinearLo, hqHinearHi, hresLo, hresHi] with
      r hr hFlo hFhi hqLolo hqLohi hqHilo hqHihi hreslo hreshi
    exact ⟨hr, hFlo, hFhi, hqLolo, hqLohi,
      hqHilo, hqHihi, hreslo, hreshi⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
  let T : ℝ := max T₀ 1
  have hTpos : 0 < T := by dsimp [T]; linarith [le_max_right T₀ 1]
  have hTdata : ∀ r, T ≤ r →
      1 ≤ r ∧
      (31 : ℝ) / 32 < F r ∧ F r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r ∧
      farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r < (33 : ℝ) / 32 ∧
      (31 : ℝ) / 32 < farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r ∧
      farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r < (33 : ℝ) / 32 ∧
      0 < farResidual n r (farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r)
        (farCandidateD1 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r) (farCandidateD2 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo r) ∧
      farResidual n r (farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r)
        (farCandidateD1 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r)
        (farCandidateD2 ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi r) < 0 := by
    intro r hr
    exact hT₀ r ((le_max_left T₀ 1).trans hr)
  let cLo : ℝ := max 0 (farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo T - F T)
  let cHi : ℝ := max 0 (F T - farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi T)
  have hcLo : 0 ≤ cLo := by dsimp [cLo]; exact le_max_left 0 _
  have hcHi : 0 ≤ cHi := by dsimp [cHi]; exact le_max_left 0 _
  have hcLosmall : cLo ≤ (1 : ℝ) / 16 := by
    dsimp [cLo]
    apply max_le (by norm_num)
    have h := hTdata T le_rfl
    linarith [h.2.1, h.2.2.2.1]
  have hcHismall : cHi ≤ (1 : ℝ) / 16 := by
    dsimp [cHi]
    apply max_le (by norm_num)
    have h := hTdata T le_rfl
    linarith [h.2.2.1, h.2.2.2.2.2.1]
  have hExp : ∀ r, T ≤ r → 0 < Real.exp (T - r) ∧
      Real.exp (T - r) ≤ 1 := by
    intro r hr
    exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩
  have htrialLonear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ sixthOrderExpBarrier ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo cLo T (-1) r := by
    intro r hr
    have hd := hTdata r (le_of_lt hr)
    have he := hExp r (le_of_lt hr)
    have hprod : cLo * Real.exp (T - r) ≤ cLo := by
      nlinarith [mul_nonneg hcLo (sub_nonneg.mpr he.2)]
    dsimp [sixthOrderExpBarrier]
    nlinarith [hd.2.2.2.1, hcLosmall]
  have htrialHinear : ∀ r, T < r →
      (9 : ℝ) / 10 ≤ sixthOrderExpBarrier ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi cHi T 1 r := by
    intro r hr
    have hd := hTdata r (le_of_lt hr)
    have hprod : 0 ≤ cHi * Real.exp (T - r) :=
      mul_nonneg hcHi (le_of_lt (Real.exp_pos _))
    dsimp [sixthOrderExpBarrier]
    nlinarith [hd.2.2.2.2.2.1]
  have hendpointLo : sixthOrderExpBarrier ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo cLo T (-1) T ≤ F T := by
    have hc : farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo T - F T ≤ cLo := by
      dsimp [cLo]; exact le_max_right _ _
    simp only [sixthOrderExpBarrier, sub_self, Real.exp_zero, mul_one]
    nlinarith
  have hendpointHi : F T ≤ sixthOrderExpBarrier ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi cHi T 1 T := by
    have hc : F T - farCandidate ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi T ≤ cHi := by
      dsimp [cHi]; exact le_max_right _ _
    simp only [sixthOrderExpBarrier, sub_self, Real.exp_zero, mul_one]
    nlinarith
  have hinftyLo : Filter.Tendsto
      (fun r => F r - sixthOrderExpBarrier ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo cLo T (-1) r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert hFone.sub
      (sixthOrderExpBarrier_tendsto_one ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vLo cLo T (-1)) using 1
    ring_nf
  have hinftyHi : Filter.Tendsto
      (fun r => sixthOrderExpBarrier ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi cHi T 1 r - F r)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (sixthOrderExpBarrier_tendsto_one
      ((n - 1) / 2) (3 * (n - 1) * (n - 5) / 8) vHi cHi T 1).sub hFone using 1
    ring_nf

  have hbelow := sixthOrder_exp_trial_comparison
    (F := F) (n := n) (a := (n - 1) / 2) (u := 3 * (n - 1) * (n - 5) / 8) (v := vLo)
    (c := cLo) (T := T) (s := 1)
    hTpos hn hcLo (by norm_num)
    hFdiff (fun r hr => hF2diff r (lt_trans hTpos hr))
    (fun r hr => hFode r (lt_trans hTpos hr))
    (by simpa using sub_nonneg.mpr hendpointLo)
    (by simpa using hinftyLo)
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.1])
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.2.2.1])
    htrialLonear
    (fun r hr => by
      simpa using le_of_lt
        (hTdata r (le_of_lt hr)).2.2.2.2.2.2.2.1)
  have habove := sixthOrder_exp_trial_comparison
    (F := F) (n := n) (a := (n - 1) / 2) (u := 3 * (n - 1) * (n - 5) / 8) (v := vHi)
    (c := cHi) (T := T) (s := -1)
    hTpos hn hcHi (by norm_num)
    hFdiff (fun r hr => hF2diff r (lt_trans hTpos hr))
    (fun r hr => hFode r (lt_trans hTpos hr))
    (by nlinarith [hendpointHi])
    (by convert hinftyHi using 1; ext r; ring_nf)
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.1])
    (fun r hr => by have h := hTdata r (le_of_lt hr); linarith [h.2.2.2.2.2.1])
    (by simpa only [neg_neg] using htrialHinear)
    (fun r hr => by
      have hres := (hTdata r (le_of_lt hr)).2.2.2.2.2.2.2.2
      nlinarith)
  refine ⟨T, cLo, cHi, hTpos, hcLo, hcHi, ?_⟩
  intro r hr
  constructor
  · have h := hbelow r hr
    linarith
  · have h := habove r hr
    nlinarith

theorem scaled6_expShift_tendsto_zero (T : ℝ) :
    Filter.Tendsto (fun r : ℝ => r ^ 6 * Real.exp (T - r))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_const_nhds (x := Real.exp T)).mul
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6)
  convert h using 1
  · ext r
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  · ring_nf

theorem scaled_sixthOrderExpBarrier
    (a u v c T s r : ℝ) (hr : r ≠ 0) :
    r ^ 6 * (sixthOrderExpBarrier a u v c T s r - 1 +
      a * r ^ (-2 : ℤ) - u * r ^ (-4 : ℤ)) =
      v + s * c * (r ^ 6 * Real.exp (T - r)) := by
  unfold sixthOrderExpBarrier farCandidate
  simp only [zpow_neg]
  field_simp [hr]
  ring

/-- The sixth-order enclosure has a definite scaled limit. This is
stronger than the `O(r⁻⁶)` estimate needed before differentiating. -/
theorem radial_profile_third_coefficient
    {F : ℝ → ℝ} {n : ℝ}
    (hn : 1 ≤ n)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 6 *
        (F r - 1 + ((n - 1) / 2) * r ^ (-2 : ℤ) -
          (3 * (n - 1) * (n - 5) / 8) * r ^ (-4 : ℤ)))
      Filter.atTop (𝓝 (farCoeff6Residual n / 2)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨T, cLo, cHi, hTpos, hcLo, hcHi, hsandwich⟩ :=
    sixthOrder_exp_sandwich hn hδ hFone hFdiff hF2diff hFode
  have htailLo : Filter.Tendsto
      (fun r : ℝ => cLo * (r ^ 6 * Real.exp (T - r)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := cLo)).mul
      (scaled6_expShift_tendsto_zero T) using 1
    ring_nf
  have htailHi : Filter.Tendsto
      (fun r : ℝ => cHi * (r ^ 6 * Real.exp (T - r)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := cHi)).mul
      (scaled6_expShift_tendsto_zero T) using 1
    ring_nf
  have hsmallLo : ∀ᶠ r : ℝ in Filter.atTop,
      cLo * (r ^ 6 * Real.exp (T - r)) < ε / 4 :=
    htailLo.eventually (eventually_lt_nhds (by linarith))
  have hsmallHi : ∀ᶠ r : ℝ in Filter.atTop,
      cHi * (r ^ 6 * Real.exp (T - r)) < ε / 4 :=
    htailHi.eventually (eventually_lt_nhds (by linarith))
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      T ≤ r ∧ 0 < r ∧
        cLo * (r ^ 6 * Real.exp (T - r)) < ε / 4 ∧
        cHi * (r ^ 6 * Real.exp (T - r)) < ε / 4 := by
    filter_upwards [Filter.eventually_ge_atTop T,
      Filter.eventually_gt_atTop (0 : ℝ), hsmallLo, hsmallHi] with
      r hr hrpos hlo hhi
    exact ⟨hr, hrpos, hlo, hhi⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro r hrN
  obtain ⟨hrT, hrpos, hsmallLoR, hsmallHiR⟩ := hN r hrN
  have ⟨hlow, hhigh⟩ := hsandwich r hrT
  have hrne : r ≠ 0 := ne_of_gt hrpos
  let a : ℝ := (n - 1) / 2
  let u : ℝ := 3 * (n - 1) * (n - 5) / 8
  let v : ℝ := farCoeff6Residual n / 2
  have hlowScaled :
      r ^ 6 *
          (sixthOrderExpBarrier a u (v - δ) cLo T (-1) r - 1 +
            a * r ^ (-2 : ℤ) - u * r ^ (-4 : ℤ)) ≤
        r ^ 6 * (F r - 1 + a * r ^ (-2 : ℤ) -
          u * r ^ (-4 : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hlow])
      (le_of_lt (pow_pos hrpos 6))
  have hhighScaled :
      r ^ 6 * (F r - 1 + a * r ^ (-2 : ℤ) -
          u * r ^ (-4 : ℤ)) ≤
        r ^ 6 *
          (sixthOrderExpBarrier a u (v + δ) cHi T 1 r - 1 +
            a * r ^ (-2 : ℤ) - u * r ^ (-4 : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hhigh])
      (le_of_lt (pow_pos hrpos 6))
  rw [scaled_sixthOrderExpBarrier _ _ _ _ _ _ r hrne] at hlowScaled hhighScaled
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> dsimp [a, u, v, δ] at * <;> nlinarith


end

end BrezisOP6
