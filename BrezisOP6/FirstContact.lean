import Mathlib

/-!
# Calculus lemma for a first contact

At a first zero approached through nonnegative values from the left, a
two-sided derivative cannot be positive. This is the analytic sign step in
the first-contact argument; the separate contact polynomial supplies the
opposite strict inequality.
-/

namespace BrezisOP6

open scoped Topology

/-- If `S r` is no larger than every value strictly to the left, then its
derivative at `r` is nonpositive. In particular this applies to the first
zero of a function positive at smaller radii. -/
theorem deriv_nonpos_at_left_min {S : ℝ → ℝ} {r d : ℝ}
    (hleft : ∀ x < r, S r ≤ S x) (hderiv : HasDerivAt S d r) : d ≤ 0 := by
  have hlim : Filter.Tendsto (slope S r) (𝓝[<] r) (𝓝 d) :=
    hderiv.tendsto_slope.mono_left (nhdsLT_le_nhdsNE r)
  have hsign : ∀ᶠ x in 𝓝[<] r, slope S r x ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxlt : x < r := hx
    have hvalue : 0 ≤ S x - S r := sub_nonneg.mpr (hleft x hxlt)
    rw [slope_def_field]
    exact div_nonpos_of_nonneg_of_nonpos hvalue (sub_nonpos.mpr (le_of_lt hxlt))
  exact le_of_tendsto hlim hsign

/-- The version used at a first zero on a positive radial interval.
Only values in `(a,r)` are needed. -/
theorem deriv_nonpos_at_first_contact {S : ℝ → ℝ} {a r d : ℝ}
    (ha : a < r) (hleft : ∀ x, a < x → x < r → S r ≤ S x)
    (hderiv : HasDerivAt S d r) : d ≤ 0 := by
  have hlim : Filter.Tendsto (slope S r) (𝓝[<] r) (𝓝 d) :=
    hderiv.tendsto_slope.mono_left (nhdsLT_le_nhdsNE r)
  have hnear : ∀ᶠ x in 𝓝[<] r, a < x :=
    (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds
  have hsign : ∀ᶠ x in 𝓝[<] r, slope S r x ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin, hnear] with x hx hax
    have hxlt : x < r := hx
    have hvalue : 0 ≤ S x - S r := sub_nonneg.mpr (hleft x hax hxlt)
    rw [slope_def_field]
    exact div_nonpos_of_nonneg_of_nonpos hvalue (sub_nonpos.mpr (le_of_lt hxlt))
  exact le_of_tendsto hlim hsign

/-- The sign contradiction used after the contact calculation: a first zero
approached from positive values cannot have positive derivative. -/
theorem no_positive_derivative_at_first_zero {S : ℝ → ℝ} {a r d : ℝ}
    (ha : a < r) (hzero : S r = 0)
    (hpositive : ∀ x, a < x → x < r → 0 < S x)
    (hderiv : HasDerivAt S d r) (hderiv_pos : 0 < d) : False := by
  have hleft : ∀ x, a < x → x < r → S r ≤ S x := by
    intro x hax hxr
    rw [hzero]
    exact le_of_lt (hpositive x hax hxr)
  have hnonpos := deriv_nonpos_at_first_contact ha hleft hderiv
  linarith

end BrezisOP6
