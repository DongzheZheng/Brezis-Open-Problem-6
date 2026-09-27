import BrezisOP6.FlowFromProfiles

/-!
# The far-field sign of the profile discrepancy

The asymptotic coefficients of the entire radial profile yield a cancellation
of the order `r⁻²` terms in `F²-(1-rF'/F)`.  The surviving coefficient is
`3(n-1)r⁻⁴`.  This module treats the expansion as precise scaled `Tendsto`
inputs and proves the sign without assuming it.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- The discrepancy used in the global profile barrier argument. -/
def infinityW (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  F r ^ 2 - profileY F r

/-- The first scaled far-field coefficient already implies `F → 1`.
This removes an otherwise redundant profile-limit input below. -/
theorem infinity_tendsto_one_of_scaled_first
    {F : ℝ → ℝ} {a : ℝ}
    (hU : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-a))) :
    Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)) := by
  have hpow : Filter.Tendsto (fun r : ℝ => r ^ 2)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hinv : Filter.Tendsto (fun r : ℝ => (r ^ 2)⁻¹)
      Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow
  have hsubscaled : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1) * (r ^ 2)⁻¹)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    convert hU.mul hinv using 1; simp
  have hsub : Filter.Tendsto (fun r : ℝ => F r - 1)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    apply hsubscaled.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    have hrne : r ≠ 0 := ne_of_gt hr
    field_simp [hrne]
  have hF : Filter.Tendsto (fun r : ℝ => (F r - 1) + 1)
      Filter.atTop (𝓝 ((0 : ℝ) + 1)) :=
    hsub.add (tendsto_const_nhds (x := (1 : ℝ)))
  simpa only [sub_add_cancel, zero_add] using hF

/-- Algebraic far-field cancellation for arbitrary expansion coefficients.
The three scaled limits are respectively the first term of `F`, its
second term, and the derivative's second term. -/
theorem infinityW_scaled_limit_general
    {F : ℝ → ℝ} {a b : ℝ}
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hU : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-a)))
    (hV : Filter.Tendsto
      (fun r : ℝ => r ^ 4 * (F r - 1) + a * r ^ 2)
      Filter.atTop (𝓝 b))
    (hQ : Filter.Tendsto
      (fun r : ℝ => r ^ 5 * deriv F r - 2 * a * r ^ 2)
      Filter.atTop (𝓝 (-4 * b))) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 4 * infinityW F r)
      Filter.atTop (𝓝 (3 * a ^ 2 - 2 * b)) := by
  have hFne : ∀ᶠ r in Filter.atTop, F r ≠ 0 :=
    hFone.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hFplus2 : Filter.Tendsto (fun r : ℝ => F r + 2)
      Filter.atTop (𝓝 (3 : ℝ)) := by
    convert hFone.add tendsto_const_nhds using 1; norm_num
  have hFplus1 : Filter.Tendsto (fun r : ℝ => F r + 1)
      Filter.atTop (𝓝 (2 : ℝ)) := by
    convert hFone.add tendsto_const_nhds using 1; norm_num
  have hratio : Filter.Tendsto (fun r : ℝ => (F r + 2) / F r)
      Filter.atTop (𝓝 (3 : ℝ)) := by
    convert hFplus2.div hFone (by norm_num : (1 : ℝ) ≠ 0)
      using 1; norm_num
  have hterm1 : Filter.Tendsto
      (fun r : ℝ => -a * (r ^ 2 * (F r - 1)) *
        ((F r + 2) / F r))
      Filter.atTop (𝓝 (3 * a ^ 2)) := by
    convert ((tendsto_const_nhds.mul hU).mul hratio) using 1; ring_nf
  have hterm2 : Filter.Tendsto
      (fun r : ℝ => (r ^ 4 * (F r - 1) + a * r ^ 2) *
        (F r + 1))
      Filter.atTop (𝓝 (2 * b)) := by
    convert hV.mul hFplus1 using 1; ring_nf
  have hterm3 : Filter.Tendsto
      (fun r : ℝ => (r ^ 5 * deriv F r - 2 * a * r ^ 2) / F r)
      Filter.atTop (𝓝 (-4 * b)) := by
    convert hQ.div hFone (by norm_num : (1 : ℝ) ≠ 0)
      using 1; ring_nf
  have hsum : Filter.Tendsto
      (fun r : ℝ =>
        -a * (r ^ 2 * (F r - 1)) * ((F r + 2) / F r) +
        (r ^ 4 * (F r - 1) + a * r ^ 2) * (F r + 1) +
        (r ^ 5 * deriv F r - 2 * a * r ^ 2) / F r)
      Filter.atTop (𝓝 (3 * a ^ 2 - 2 * b)) := by
    convert (hterm1.add hterm2).add hterm3 using 1; ring_nf
  apply hsum.congr'
  filter_upwards [hFne] with r hr
  unfold infinityW profileY
  field_simp [hr]
  ring_nf

/-- Coefficients of the `r⁻²` and `r⁻⁴` terms of the entire profile. -/
def infinityCoeff2 (n : ℕ) : ℝ := ((n : ℝ) - 1) / 2

def infinityCoeff4 (n : ℕ) : ℝ :=
  3 * ((n : ℝ) - 1) * ((n : ℝ) - 5) / 8

/-- The exact first nonzero term:
`r⁴(F²-y) → 3(n-1)`. -/
theorem infinityW_scaled_limit
    (n : ℕ) {F : ℝ → ℝ}
    (hU : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-infinityCoeff2 n)))
    (hV : Filter.Tendsto
      (fun r : ℝ => r ^ 4 * (F r - 1) +
        infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (infinityCoeff4 n)))
    (hQ : Filter.Tendsto
      (fun r : ℝ => r ^ 5 * deriv F r -
        2 * infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (-4 * infinityCoeff4 n))) :
    Filter.Tendsto
      (fun r : ℝ => r ^ 4 * infinityW F r)
      Filter.atTop (𝓝 (3 * ((n : ℝ) - 1))) := by
  have h := infinityW_scaled_limit_general
    (a := infinityCoeff2 n) (b := infinityCoeff4 n)
    (infinity_tendsto_one_of_scaled_first hU) hU hV hQ
  convert h using 1
  unfold infinityCoeff2 infinityCoeff4
  ring_nf

/-- For every dimension `n≥3`, the positive leading coefficient gives
eventual strict positivity of `F²-y`. -/
theorem infinityW_eventually_pos
    (n : ℕ) {F : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hU : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-infinityCoeff2 n)))
    (hV : Filter.Tendsto
      (fun r : ℝ => r ^ 4 * (F r - 1) +
        infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (infinityCoeff4 n)))
    (hQ : Filter.Tendsto
      (fun r : ℝ => r ^ 5 * deriv F r -
        2 * infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (-4 * infinityCoeff4 n))) :
    ∀ᶠ r : ℝ in Filter.atTop, 0 < infinityW F r := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlead : 0 < 3 * ((n : ℝ) - 1) := by linarith
  have hlim := infinityW_scaled_limit n hU hV hQ
  have hscaled : ∀ᶠ r : ℝ in Filter.atTop,
      0 < r ^ 4 * infinityW F r :=
    hlim.eventually (eventually_gt_nhds hlead)
  have hrpos : ∀ᶠ r : ℝ in Filter.atTop, 0 < r :=
    Filter.eventually_gt_atTop 0
  filter_upwards [hscaled, hrpos] with r hscaled hr
  by_contra hnot
  have hWle : infinityW F r ≤ 0 := le_of_not_gt hnot
  have hp : r ^ 4 * infinityW F r ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt (pow_pos hr 4)) hWle
  linarith

end

end BrezisOP6
