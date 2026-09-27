import BrezisOP6.Ratio

/-!
# Global logarithmic-slope bound for one radial profile

The regular-origin flux starts at zero. The radial ODE makes its derivative
strictly negative when `0<p<1` in the open ball, so `r p'/p<1` follows
through the outer endpoint. The endpoint value `p(R)=1` is allowed.
This is the profile input for the normalized ratio-growth bound.
-/

namespace BrezisOP6

noncomputable section

/-- An initially zero flux with negative derivative stays negative. -/
theorem flux_neg_of_deriv_neg
    {q : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hqcont : ContinuousOn q (Set.Icc 0 R))
    (hq0 : q 0 = 0)
    (hderiv : ∀ r ∈ Set.Ioo 0 R, deriv q r < 0) :
    ∀ r ∈ Set.Ioc 0 R, q r < 0 := by
  have hanti : StrictAntiOn q (Set.Icc 0 R) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 R) hqcont
    intro r hr
    exact hderiv r (by simpa using hr)
  intro r hr
  have h0I : (0 : ℝ) ∈ Set.Icc 0 R :=
    ⟨le_rfl, le_of_lt hR⟩
  have hrI : r ∈ Set.Icc 0 R :=
    ⟨le_of_lt hr.1, hr.2⟩
  have h := hanti h0I hrI hr.1
  rwa [hq0] at h

/-- The single-profile flux is strictly negative through the outer endpoint,
using the ODE and `p<1` only at interior radii. -/
theorem profile_slope_flux_neg
    (d : ℕ) (p : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hpDiff : Differentiable ℝ p)
    (hfluxcont : ContinuousOn (slopeFlux (d + 1) p) (Set.Icc 0 R))
    (hpos : ∀ r ∈ Set.Ioc 0 R, 0 < p r)
    (hlt : ∀ r ∈ Set.Ioo 0 R, p r < 1)
    (hODE : ∀ r ∈ Set.Ioo 0 R,
      ∃ p₂ : ℝ,
        HasDerivAt (deriv p) p₂ r ∧
        p₂ + ((d : ℝ) + 1) / r * deriv p r -
          ((d : ℝ) + 1) / r ^ 2 * p r +
          (1 - p r ^ 2) * p r = 0) :
    ∀ r ∈ Set.Ioc 0 R, slopeFlux (d + 1) p r < 0 := by
  have hq0 : slopeFlux (d + 1) p 0 = 0 := by
    simp [slopeFlux]
  apply flux_neg_of_deriv_neg hR hfluxcont hq0
  intro r hr
  obtain ⟨p₂, hp₂, hode⟩ := hODE r hr
  have hp₁ : HasDerivAt p (deriv p r) r :=
    (hpDiff r).hasDerivAt
  rw [(slopeFlux_hasDerivAt d (ne_of_gt hr.1) hp₁ hp₂ hode).deriv]
  have hp : 0 < p r := hpos r ⟨hr.1, le_of_lt hr.2⟩
  have hpl : p r < 1 := hlt r hr
  have hs : 0 < 1 - p r ^ 2 := by nlinarith
  have hpow : 0 < r ^ (d + 2) := pow_pos hr.1 _
  have hprod : 0 < r ^ (d + 2) * (1 - p r ^ 2) * p r :=
    mul_pos (mul_pos hpow hs) hp
  linarith

/-- The ODE and regular-origin flux give the strict upper bound for the
logarithmic radial slope of the profile. -/
theorem profile_logSlope_lt_one
    (d : ℕ) (p : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hpDiff : Differentiable ℝ p)
    (hfluxcont : ContinuousOn (slopeFlux (d + 1) p) (Set.Icc 0 R))
    (hpos : ∀ r ∈ Set.Ioc 0 R, 0 < p r)
    (hlt : ∀ r ∈ Set.Ioo 0 R, p r < 1)
    (hODE : ∀ r ∈ Set.Ioo 0 R,
      ∃ p₂ : ℝ,
        HasDerivAt (deriv p) p₂ r ∧
        p₂ + ((d : ℝ) + 1) / r * deriv p r -
          ((d : ℝ) + 1) / r ^ 2 * p r +
          (1 - p r ^ 2) * p r = 0) :
    ∀ r ∈ Set.Ioc 0 R,
      r * deriv p r / p r < 1 := by
  have hflux := profile_slope_flux_neg d p R hR hpDiff
    hfluxcont hpos hlt hODE
  intro r hr
  exact logSlope_lt_one hr.1 (hpos r hr) (hflux r hr)

end

end BrezisOP6
