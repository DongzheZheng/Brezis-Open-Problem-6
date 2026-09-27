import Mathlib

/-!
# The ratio identity for two radial Ginzburg--Landau profiles

Write `m = n - 1` for the spherical Jacobian exponent.  The equation

`p'' + (m/r) p' - (m/r²) p + (1-p²)p = 0`

is used only through its value at the positive radius under consideration.
The main invariant is the weighted Wronskian `r^m (F f' - f F')`.
The final lemma identifies that invariant with `r^m F² (f/F)'` whenever
`F` is nonzero.  Thus its derivative is precisely the source term
`r^m F⁴ (f/F) ((f/F)² - 1)` in the paper.
-/

namespace BrezisOP6

noncomputable section
open scoped Topology

/-- The weighted Wronskian of radial profiles `f` and `F`. -/
def ratioFlux (m : ℕ) (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ m * (F r * deriv f r - f r * deriv F r)

/-- Differentiating a profile quotient at a point where the denominator is
nonzero gives its Wronskian numerator. -/
theorem ratio_deriv_formula {f F : ℝ → ℝ} {r : ℝ}
    (hf : DifferentiableAt ℝ f r) (hF : DifferentiableAt ℝ F r)
    (hF0 : F r ≠ 0) :
    deriv (fun t => f t / F t) r =
      (F r * deriv f r - f r * deriv F r) / (F r) ^ 2 := by
  have h := (hf.hasDerivAt.div hF.hasDerivAt hF0).deriv
  convert h using 1
  ring

/-- Pointwise identification of the paper's ratio flux with the weighted
Wronskian. -/
theorem ratioFlux_eq_ratio (m : ℕ) {f F : ℝ → ℝ} {r : ℝ}
    (hf : DifferentiableAt ℝ f r) (hF : DifferentiableAt ℝ F r)
    (hF0 : F r ≠ 0) :
    ratioFlux m f F r =
      r ^ m * (F r) ^ 2 * deriv (fun t => f t / F t) r := by
  rw [ratio_deriv_formula hf hF hF0]
  unfold ratioFlux
  field_simp [hF0]

/-- Subtracting two radial profile equations differentiates the weighted
Wronskian.  The assumptions `hf2` and `hF2` provide only second-order
differentiability at `r`; no global ODE theorem is hidden in this statement. -/
theorem ratioFlux_hasDerivAt (d : ℕ) {f F : ℝ → ℝ} {r f₁ F₁ f₂ F₂ : ℝ}
    (hr : r ≠ 0)
    (hf : HasDerivAt f f₁ r) (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hode_f : f₂ + ((d : ℝ) + 1) / r * f₁ -
      ((d : ℝ) + 1) / r ^ 2 * f r + (1 - (f r) ^ 2) * f r = 0)
    (hode_F : F₂ + ((d : ℝ) + 1) / r * F₁ -
      ((d : ℝ) + 1) / r ^ 2 * F r + (1 - (F r) ^ 2) * F r = 0) :
    HasDerivAt (ratioFlux (d + 1) f F)
      (r ^ (d + 1) * F r * f r * ((f r) ^ 2 - (F r) ^ 2)) r := by
  have hfp : deriv f r = f₁ := hf.deriv
  have hFp : deriv F r = F₁ := hF.deriv
  have hW : HasDerivAt
      (fun t => F t * deriv f t - f t * deriv F t)
      (F r * f₂ - f r * F₂) r := by
    convert (hF.mul hdf).sub (hf.mul hdF) using 1
    simp only [hfp, hFp]
    ring
  have hpow : HasDerivAt (fun t : ℝ => t ^ (d + 1))
      (((d : ℝ) + 1) * r ^ d) r := by
    convert (hasDerivAt_id r).pow (d + 1) using 1
    simp
  have hraw := hpow.mul hW
  have hf₂ : f₂ = -((d : ℝ) + 1) / r * f₁ +
      ((d : ℝ) + 1) / r ^ 2 * f r - (1 - (f r) ^ 2) * f r := by
    ring_nf at hode_f ⊢
    linarith
  have hF₂ : F₂ = -((d : ℝ) + 1) / r * F₁ +
      ((d : ℝ) + 1) / r ^ 2 * F r - (1 - (F r) ^ 2) * F r := by
    ring_nf at hode_F ⊢
    linarith
  have hcore :
      (((d : ℝ) + 1) * r ^ d) *
        (F r * deriv f r - f r * deriv F r) +
      r ^ (d + 1) * (F r * f₂ - f r * F₂) =
      r ^ (d + 1) * F r * f r * ((f r) ^ 2 - (F r) ^ 2) := by
    rw [hfp, hFp, hf₂, hF₂, pow_succ]
    field_simp [hr]
    ring
  simpa only [ratioFlux, hcore] using hraw

/-- The derivative of the weighted Wronskian equals the source term in the
profile-ratio equation. -/
theorem deriv_ratioFlux (d : ℕ) {f F : ℝ → ℝ} {r f₁ F₁ f₂ F₂ : ℝ}
    (hr : r ≠ 0)
    (hf : HasDerivAt f f₁ r) (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hode_f : f₂ + ((d : ℝ) + 1) / r * f₁ -
      ((d : ℝ) + 1) / r ^ 2 * f r + (1 - (f r) ^ 2) * f r = 0)
    (hode_F : F₂ + ((d : ℝ) + 1) / r * F₁ -
      ((d : ℝ) + 1) / r ^ 2 * F r + (1 - (F r) ^ 2) * F r = 0) :
    deriv (ratioFlux (d + 1) f F) r =
      r ^ (d + 1) * F r * f r * ((f r) ^ 2 - (F r) ^ 2) :=
  (ratioFlux_hasDerivAt d hr hf hF hdf hdF hode_f hode_F).deriv

/-- The ratio identity in exactly the form used in the analytic proof:
`(r^m F² (f/F)')' = r^m F⁴ (f/F) ((f/F)² - 1)` with `m = d + 1`.
The global differentiability hypotheses serve only to identify the two flux
functions on a neighborhood of `r`; the ODE is needed only at `r`. -/
theorem weighted_ratio_hasDerivAt (d : ℕ) {f F : ℝ → ℝ}
    {r f₁ F₁ f₂ F₂ : ℝ}
    (hr : r ≠ 0) (hF0 : F r ≠ 0)
    (hDiff_f : Differentiable ℝ f) (hDiff_F : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ r) (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hode_f : f₂ + ((d : ℝ) + 1) / r * f₁ -
      ((d : ℝ) + 1) / r ^ 2 * f r + (1 - (f r) ^ 2) * f r = 0)
    (hode_F : F₂ + ((d : ℝ) + 1) / r * F₁ -
      ((d : ℝ) + 1) / r ^ 2 * F r + (1 - (F r) ^ 2) * F r = 0) :
    HasDerivAt
      (fun t => t ^ (d + 1) * (F t) ^ 2 *
        deriv (fun s => f s / F s) t)
      (r ^ (d + 1) * (F r) ^ 4 * (f r / F r) *
        ((f r / F r) ^ 2 - 1)) r := by
  have hFne : ∀ᶠ t in 𝓝 r, F t ≠ 0 :=
    hF.continuousAt.eventually (eventually_ne_nhds hF0)
  have hEq :
      (fun t => t ^ (d + 1) * (F t) ^ 2 *
        deriv (fun s => f s / F s) t) =ᶠ[𝓝 r]
      ratioFlux (d + 1) f F := by
    filter_upwards [hFne] with t ht
    exact (ratioFlux_eq_ratio (d + 1) (hDiff_f t) (hDiff_F t) ht).symm
  have hFlux := (ratioFlux_hasDerivAt d hr hf hF hdf hdF hode_f hode_F)
  have hAlgebra :
      r ^ (d + 1) * F r * f r * ((f r) ^ 2 - (F r) ^ 2) =
      r ^ (d + 1) * (F r) ^ 4 * (f r / F r) *
        ((f r / F r) ^ 2 - 1) := by
    field_simp [hF0]
  simpa only [hAlgebra] using hFlux.congr_of_eventuallyEq hEq

/-- Ordinary-derivative version of `weighted_ratio_hasDerivAt`. -/
theorem deriv_weighted_ratio (d : ℕ) {f F : ℝ → ℝ}
    {r f₁ F₁ f₂ F₂ : ℝ}
    (hr : r ≠ 0) (hF0 : F r ≠ 0)
    (hDiff_f : Differentiable ℝ f) (hDiff_F : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ r) (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hode_f : f₂ + ((d : ℝ) + 1) / r * f₁ -
      ((d : ℝ) + 1) / r ^ 2 * f r + (1 - (f r) ^ 2) * f r = 0)
    (hode_F : F₂ + ((d : ℝ) + 1) / r * F₁ -
      ((d : ℝ) + 1) / r ^ 2 * F r + (1 - (F r) ^ 2) * F r = 0) :
    deriv (fun t => t ^ (d + 1) * (F t) ^ 2 *
      deriv (fun s => f s / F s) t) r =
      r ^ (d + 1) * (F r) ^ 4 * (f r / F r) *
        ((f r / F r) ^ 2 - 1) :=
  (weighted_ratio_hasDerivAt d hr hF0 hDiff_f hDiff_F hf hF hdf hdF
    hode_f hode_F).deriv

/-- The flux controlling the logarithmic slope of a single profile. -/
def slopeFlux (m : ℕ) (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ m * (r * deriv p r - p r)

/-- The second first-order identity used in the paper.  In the notation
`A=p/r`, this is the equivalent of
`(r^(n+1) A')' = -r^(n+1) (1-p²) A`, with `n=d+2`. -/
theorem slopeFlux_hasDerivAt (d : ℕ) {p : ℝ → ℝ}
    {r p₁ p₂ : ℝ} (hr : r ≠ 0)
    (hp : HasDerivAt p p₁ r)
    (hdp : HasDerivAt (deriv p) p₂ r)
    (hode : p₂ + ((d : ℝ) + 1) / r * p₁ -
      ((d : ℝ) + 1) / r ^ 2 * p r + (1 - (p r) ^ 2) * p r = 0) :
    HasDerivAt (slopeFlux (d + 1) p)
      (-r ^ (d + 2) * (1 - (p r) ^ 2) * p r) r := by
  have hp₁ : deriv p r = p₁ := hp.deriv
  have hW : HasDerivAt (fun t => t * deriv p t - p t)
      (r * p₂) r := by
    convert ((hasDerivAt_id r).mul hdp).sub hp using 1
    simp only [hp₁, id_eq]
    ring
  have hpow : HasDerivAt (fun t : ℝ => t ^ (d + 1))
      (((d : ℝ) + 1) * r ^ d) r := by
    convert (hasDerivAt_id r).pow (d + 1) using 1
    simp
  have hraw := hpow.mul hW
  have hp₂ : p₂ = -((d : ℝ) + 1) / r * p₁ +
      ((d : ℝ) + 1) / r ^ 2 * p r - (1 - (p r) ^ 2) * p r := by
    ring_nf at hode ⊢
    linarith
  have hcore :
      (((d : ℝ) + 1) * r ^ d) * (r * deriv p r - p r) +
      r ^ (d + 1) * (r * p₂) =
      -r ^ (d + 2) * (1 - (p r) ^ 2) * p r := by
    rw [hp₁, hp₂, pow_succ, pow_succ]
    field_simp [hr]
    ring
  simpa only [slopeFlux, hcore] using hraw

/-- A negative slope flux gives the upper logarithmic-slope bound.  The
strict negativity itself follows in analysis by integrating
`slopeFlux_hasDerivAt` from the regular origin when `0 < p < 1`. -/
theorem logSlope_lt_one {m : ℕ} {p : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hp : 0 < p r)
    (hflux : slopeFlux m p r < 0) :
    r * deriv p r / p r < 1 := by
  unfold slopeFlux at hflux
  have hrm : 0 < r ^ m := pow_pos hr _
  have hcore : r * deriv p r - p r < 0 := by
    by_contra hn
    have hnonneg : 0 ≤ r * deriv p r - p r := le_of_not_gt hn
    have : 0 ≤ r ^ m * (r * deriv p r - p r) :=
      mul_nonneg (le_of_lt hrm) hnonneg
    linarith
  apply (div_lt_iff₀ hp).2
  nlinarith

end

end BrezisOP6
