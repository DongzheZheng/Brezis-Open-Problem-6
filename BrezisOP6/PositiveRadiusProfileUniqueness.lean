import BrezisOP6.PositiveRadiusLinearUniqueness

/-!
# Positive-radius initial-value uniqueness for two radial profiles

This discharges the ordinary, nonsingular ODE-uniqueness input used to
propagate the independently proved origin germ.  The finite-ball ODE is
needed only at radii strictly between zero and the outer sphere.  Equality
at the outer sphere follows from the continuous trace of both profiles.
-/

namespace BrezisOP6

open Set Filter
open scoped Topology

noncomputable section

theorem radial_profile_positive_radius_ivp_unique
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ) (R : ℝ)
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
        r (F r) (deriv F r) (F₂ r)) :
    ∀ s ∈ Ioo (0 : ℝ) R,
      f s = F s → deriv f s = deriv F s →
      ∀ r ∈ Ioc (0 : ℝ) R, f r = F r := by
  let A : ℝ → ℝ :=
    fun t => radialDifferenceCoefficient ((m : ℝ) + 3) t (f t) (F t)
  let B : ℝ → ℝ := fun t => -((((m : ℝ) + 3) - 1) / t)
  let d : ℝ → ℝ := fun t => f t - F t
  let e : ℝ → ℝ := fun t => deriv f t - deriv F t
  intro s hs hfs hdfs r hr
  have hlocal (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) : f t = F t := by
    let a := min s t / 2
    have ha0 : 0 < a := by
      dsimp [a]
      have hmin : 0 < min s t := lt_min hs.1 ht.1
      linarith
    have has : a < s := by
      dsimp [a]
      have hmin : min s t ≤ s := min_le_left _ _
      have hminpos : 0 < min s t := lt_min hs.1 ht.1
      linarith
    have hat : a < t := by
      dsimp [a]
      have hmin : min s t ≤ t := min_le_right _ _
      have hminpos : 0 < min s t := lt_min hs.1 ht.1
      linarith
    have hAcont : ContinuousOn A (Icc a R) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ha0 hx.1
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hfcont : ContinuousAt f x := (hfDiff x).continuousAt
      have hFcont : ContinuousAt F x := (hFDiff x).continuousAt
      have hdiv : ContinuousAt
          (fun q : ℝ => (((m : ℝ) + 3) - 1) / q ^ 2) x :=
        continuousAt_const.div (continuousAt_id.pow 2)
          (pow_ne_zero 2 hxne)
      have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x :=
        continuousAt_const
      have hraw : ContinuousAt
          (fun q : ℝ =>
            (((m : ℝ) + 3) - 1) / q ^ 2 - 1 + f q ^ 2 +
              f q * F q + F q ^ 2) x :=
        ((((hdiv.sub hone).add (hfcont.pow 2)).add
          (hfcont.mul hFcont)).add (hFcont.pow 2))
      exact (show ContinuousAt A x by
        simpa only [A, radialDifferenceCoefficient] using hraw).continuousWithinAt
    have hBcont : ContinuousOn B (Icc a R) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ha0 hx.1
      have hdiv : ContinuousAt
          (fun q : ℝ => (((m : ℝ) + 3) - 1) / q) x :=
        continuousAt_const.div continuousAt_id (ne_of_gt hxpos)
      exact (show ContinuousAt B x by
        simpa only [B] using hdiv.neg).continuousWithinAt
    have hd' (x : ℝ) (hx : x ∈ Ioo a R) :
        HasDerivAt d (e x) x := by
      simpa only [d, e] using
        (hfDiff x).hasDerivAt.sub (hFDiff x).hasDerivAt
    have he' (x : ℝ) (hx : x ∈ Ioo a R) :
        HasDerivAt e (A x * d x + B x * e x) x := by
      have hx' : x ∈ Ioo (0 : ℝ) R :=
        ⟨lt_trans ha0 hx.1, hx.2⟩
      have hlinear := radialODE_difference_linear
        ((m : ℝ) + 3) x (f x) (F x)
        (deriv f x) (deriv F x) (f₂ x) (F₂ x)
        hx'.1 (hode_f x hx') (hode_F x hx')
      have hderiv := (hdf x hx').sub (hdF x hx')
      convert hderiv using 1
      simpa only [A, B, d, e, neg_mul, sub_eq_add_neg]
        using hlinear.symm
    have hds : d s = 0 := by simp [d, hfs]
    have hes : e s = 0 := by simp [e, hdfs]
    have heq := linear_difference_pair_zero_of_continuous_coefficients
      A B d e a R s has hs.2 hAcont hBcont hd' he' hds hes t ⟨hat, ht.2⟩
    exact sub_eq_zero.mp heq.1
  by_cases hrt : r < R
  · exact hlocal r ⟨hr.1, hrt⟩
  · have hrR : r = R := le_antisymm hr.2 (le_of_not_gt hrt)
    subst r
    have hpos : ∀ᶠ t in 𝓝[<] R, 0 < t :=
      (eventually_gt_nhds (hs.1.trans hs.2)).filter_mono
        nhdsWithin_le_nhds
    have hevent : f =ᶠ[𝓝[<] R] F := by
      filter_upwards [self_mem_nhdsWithin, hpos] with t htlt htpos
      exact hlocal t ⟨htpos, htlt⟩
    have hlimf : Tendsto f (𝓝[<] R) (𝓝 (f R)) :=
      ((hfDiff R).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hlimF : Tendsto F (𝓝[<] R) (𝓝 (F R)) :=
      ((hFDiff R).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlimf ((tendsto_congr' hevent).2 hlimF)

end

end BrezisOP6
