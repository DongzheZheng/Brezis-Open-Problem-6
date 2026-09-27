import BrezisOP6.OriginTaylorInterior
import Mathlib.Analysis.Calculus.Taylor

/-!
# Differentiated origin expansion from a smooth radial factor

The existing profile theorem supplies a local representation
`p(r) = r * H(r²)` with `H` smooth near zero.  This file derives the
three differentiated Peano expansions used by `RadialOriginTaylorInterior`.
The radial ODE is subsequently used by `radial_origin_coefficients_on_localTaylor`
to determine the coefficients; no coefficient is built into this regularity
argument.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

private theorem smooth_factor_first_derivative
    (H : ℝ → ℝ) (hH : ContDiff ℝ 2 H) (r : ℝ) :
    deriv (fun t : ℝ => t * H (t ^ 2)) r =
      H (r ^ 2) + 2 * r ^ 2 * deriv H (r ^ 2) := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
    convert hasDerivAt_pow 2 r using 1 <;> ring
  have hcomp : HasDerivAt (fun t : ℝ => H (t ^ 2))
      (deriv H (r ^ 2) * (2 * r)) r :=
    ((hH.of_le (by norm_num)).differentiable_one (r ^ 2)).hasDerivAt.comp r hpow
  calc
    deriv (fun t : ℝ => t * H (t ^ 2)) r =
        H (r ^ 2) + r * (deriv H (r ^ 2) * (2 * r)) := by
      simpa [Pi.mul_apply, id_eq] using ((hasDerivAt_id r).mul hcomp).deriv
    _ = H (r ^ 2) + 2 * r ^ 2 * deriv H (r ^ 2) := by ring

private theorem smooth_factor_second_derivative
    (H : ℝ → ℝ) (hH : ContDiff ℝ 2 H) (r : ℝ) :
    deriv (deriv (fun t : ℝ => t * H (t ^ 2))) r =
      6 * r * deriv H (r ^ 2) +
        4 * r ^ 3 * deriv (deriv H) (r ^ 2) := by
  have hfirst : deriv (fun t : ℝ => t * H (t ^ 2)) =
      fun t : ℝ => H (t ^ 2) + 2 * t ^ 2 * deriv H (t ^ 2) := by
    funext t
    exact smooth_factor_first_derivative H hH t
  rw [hfirst]
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
    convert hasDerivAt_pow 2 r using 1 <;> ring
  have hA : HasDerivAt (fun t : ℝ => H (t ^ 2))
      (deriv H (r ^ 2) * (2 * r)) r :=
    ((hH.of_le (by norm_num)).differentiable_one (r ^ 2)).hasDerivAt.comp r hpow
  have hDcont : ContDiff ℝ 1 (deriv H) := by
    exact (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) H by
      simpa using hH)).2.2
  have hD' : HasDerivAt (deriv H)
      (deriv (deriv H) (r ^ 2)) (r ^ 2) :=
    (hDcont.differentiable_one (r ^ 2)).hasDerivAt
  have hB : HasDerivAt (fun t : ℝ => deriv H (t ^ 2))
      (deriv (deriv H) (r ^ 2) * (2 * r)) r :=
    by simpa only [Function.comp_def] using
      (hD'.comp_of_eq r hpow (show r ^ 2 = (fun t : ℝ => t ^ 2) r by rfl))
  have hC : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * r) r := by
    convert hpow.const_mul 2 using 1 <;> ring
  have hterm := hA.add (hC.mul hB)
  calc
    deriv (fun t : ℝ => H (t ^ 2) +
      2 * t ^ 2 * deriv H (t ^ 2)) r =
        deriv H (r ^ 2) * (2 * r) +
        ((4 * r) * deriv H (r ^ 2) +
          (2 * r ^ 2) * (deriv (deriv H) (r ^ 2) * (2 * r))) := by
      simpa [Pi.mul_apply] using hterm.deriv
    _ = 6 * r * deriv H (r ^ 2) +
        4 * r ^ 3 * deriv (deriv H) (r ^ 2) := by ring

private theorem smooth_factor_taylor_two
    (H : ℝ → ℝ) (hH : ContDiff ℝ 2 H) :
    Tendsto (fun s : ℝ =>
      (H s - H 0 - deriv H 0 * s -
        (deriv (deriv H) 0 / 2) * s ^ 2) / s ^ 2)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hTaylor := Real.taylor_tendsto convex_univ (mem_univ (0 : ℝ)) hH.contDiffOn
  have hpoly : ∀ s : ℝ,
      taylorWithinEval H 2 univ 0 s =
        H 0 + deriv H 0 * s + (deriv (deriv H) 0 / 2) * s ^ 2 := by
    intro s
    simp only [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_univ, iteratedDeriv_succ,
      iteratedDeriv_zero, iteratedDeriv_one]
    norm_num
    ring
  convert (show Tendsto (fun s : ℝ =>
      (H s - taylorWithinEval H 2 univ 0 s) / (s - 0) ^ 2)
      (𝓝 (0 : ℝ)) (𝓝 0) by simpa only [nhdsWithin_univ] using hTaylor) using 1
  funext s
  rw [hpoly]
  ring

private theorem smooth_factor_taylor_one
    (H : ℝ → ℝ) (hH : ContDiff ℝ 2 H) :
    Tendsto (fun s : ℝ =>
      (deriv H s - deriv H 0 - deriv (deriv H) 0 * s) / s)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hH' : ContDiff ℝ 1 (deriv H) := by
    exact (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) H by
      simpa using hH)).2.2
  have hTaylor := Real.taylor_tendsto convex_univ (mem_univ (0 : ℝ)) hH'.contDiffOn
  have hpoly : ∀ s : ℝ,
      taylorWithinEval (deriv H) 1 univ 0 s =
        deriv H 0 + deriv (deriv H) 0 * s := by
    intro s
    simp only [taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_univ, iteratedDeriv_one]
    norm_num
    ring
  convert (show Tendsto (fun s : ℝ =>
      (deriv H s - taylorWithinEval (deriv H) 1 univ 0 s) /
        (s - 0) ^ 1)
      (𝓝 (0 : ℝ)) (𝓝 0) by simpa only [nhdsWithin_univ] using hTaylor) using 1
  funext s
  rw [hpoly]
  ring

/-- The paper's local smooth factorization supplies all three differentiated
order-five Peano remainders.  This requires `C²` of `H`, which is contained in
the paper's stated smooth origin regularity. -/
noncomputable def radialOriginTaylorInterior_of_smooth_factor
    (p H : ℝ → ℝ) (R : ℝ)
    (hH : ContDiff ℝ 2 H)
    (hFactor : ∀ r : ℝ, 0 < r → r < R → p r = r * H (r ^ 2)) :
    RadialOriginTaylorInterior p (H 0) (deriv H 0)
      (deriv (deriv H) 0 / 2) R := by
  let q₀ : ℝ → ℝ := fun s =>
    (H s - H 0 - deriv H 0 * s -
      (deriv (deriv H) 0 / 2) * s ^ 2) / s ^ 2
  let q₁ : ℝ → ℝ := fun s =>
    (deriv H s - deriv H 0 - deriv (deriv H) 0 * s) / s
  have hq₀ : Tendsto q₀ (𝓝 (0 : ℝ)) (𝓝 0) :=
    smooth_factor_taylor_two H hH
  have hq₁ : Tendsto q₁ (𝓝 (0 : ℝ)) (𝓝 0) :=
    smooth_factor_taylor_one H hH
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hs : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hr.pow 2 using 1 <;> norm_num
  have hq₀r : Tendsto (fun r : ℝ => q₀ (r ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hq₀.comp hs
  have hq₁r : Tendsto (fun r : ℝ => q₁ (r ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hq₁.comp hs
  have hD2 : Tendsto (fun r : ℝ => deriv (deriv H) (r ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv H) 0)) := by
    have hH' : ContDiff ℝ 1 (deriv H) := by
      exact (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) H by
        simpa using hH)).2.2
    exact hH'.continuous_deriv_one.continuousAt.tendsto.comp hs
  let g : ℝ → ℝ := fun r => r * H (r ^ 2)
  have hlocal (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      p =ᶠ[𝓝 r] g := by
    filter_upwards [isOpen_Ioo.mem_nhds (show r ∈ Ioo (0 : ℝ) R from ⟨hr, hrR⟩)]
      with t ht
    exact hFactor t ht.1 ht.2
  have hfirst (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      deriv p r = H (r ^ 2) + 2 * r ^ 2 * deriv H (r ^ 2) := by
    rw [(hlocal r hr hrR).deriv_eq]
    exact smooth_factor_first_derivative H hH r
  have hsecond (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      deriv (deriv p) r =
        6 * r * deriv H (r ^ 2) +
          4 * r ^ 3 * deriv (deriv H) (r ^ 2) := by
    rw [((hlocal r hr hrR).deriv).deriv_eq]
    exact smooth_factor_second_derivative H hH r
  refine ⟨(fun r => q₀ (r ^ 2)),
    (fun r => q₀ (r ^ 2) + 2 * q₁ (r ^ 2)),
    (fun r => 6 * q₁ (r ^ 2) +
      4 * (deriv (deriv H) (r ^ 2) - deriv (deriv H) 0)),
    ?_, ?_, ?_, hq₀r, ?_, ?_⟩
  · intro r hr hrR
    rw [hFactor r hr hrR]
    dsimp [q₀]
    field_simp [pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hr))]
    ring
  · intro r hr hrR
    rw [hfirst r hr hrR]
    dsimp [q₀, q₁]
    field_simp [pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hr)),
      pow_ne_zero 2 (ne_of_gt hr)]
    ring
  · intro r hr hrR
    rw [hsecond r hr hrR]
    dsimp [q₁]
    field_simp [pow_ne_zero 2 (ne_of_gt hr)]
    ring
  · convert hq₀r.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hq₁r)
      using 1 <;> simp
  · convert ((tendsto_const_nhds (x := (6 : ℝ))).mul hq₁r).add
      ((tendsto_const_nhds (x := (4 : ℝ))).mul
        (hD2.sub tendsto_const_nhds)) using 1 <;> simp

/-- The order-five Peano expansion is a germ at zero.  A proof on an
arbitrarily small interval can be extended to the chosen ball radius by
defining its error functions algebraically at the other radii. -/
noncomputable def RadialOriginTaylorInterior.extendOuter
    {p : ℝ → ℝ} {α A B δ : ℝ} (h : RadialOriginTaylorInterior p α A B δ)
    (hδ : 0 < δ) (R : ℝ) :
    RadialOriginTaylorInterior p α A B R := by
  let e₀ : ℝ → ℝ := fun r =>
    if r < δ then h.e₀ r else
      (p r - α * r - A * r ^ 3 - B * r ^ 5) / r ^ 5
  let e₁ : ℝ → ℝ := fun r =>
    if r < δ then h.e₁ r else
      (deriv p r - α - 3 * A * r ^ 2 - 5 * B * r ^ 4) / r ^ 4
  let e₂ : ℝ → ℝ := fun r =>
    if r < δ then h.e₂ r else
      (deriv (deriv p) r - 6 * A * r - 20 * B * r ^ 3) / r ^ 3
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  refine ⟨e₀, e₁, e₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr _
    by_cases hlt : r < δ
    · change p r = α * r + A * r ^ 3 + B * r ^ 5 +
        r ^ 5 * (if r < δ then h.e₀ r else _)
      simpa [hlt] using h.value r hr hlt
    · change p r = α * r + A * r ^ 3 + B * r ^ 5 +
        r ^ 5 * (if r < δ then h.e₀ r else _)
      rw [if_neg hlt]
      field_simp [pow_ne_zero 5 (ne_of_gt hr)]
      ring
  · intro r hr _
    by_cases hlt : r < δ
    · change deriv p r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * (if r < δ then h.e₁ r else _)
      simpa [hlt] using h.first r hr hlt
    · change deriv p r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * (if r < δ then h.e₁ r else _)
      rw [if_neg hlt]
      field_simp [pow_ne_zero 4 (ne_of_gt hr)]
      ring
  · intro r hr _
    by_cases hlt : r < δ
    · change deriv (deriv p) r =
        6 * A * r + 20 * B * r ^ 3 +
          r ^ 3 * (if r < δ then h.e₂ r else _)
      simpa [hlt] using h.second r hr hlt
    · change deriv (deriv p) r =
        6 * A * r + 20 * B * r ^ 3 +
          r ^ 3 * (if r < δ then h.e₂ r else _)
      rw [if_neg hlt]
      field_simp [pow_ne_zero 3 (ne_of_gt hr)]
      ring
  · have heq : e₀ =ᶠ[𝓝[>] (0 : ℝ)] h.e₀ := by
      filter_upwards [hsmall] with r hr
      simp [e₀, hr]
    exact (tendsto_congr' heq).2 h.e₀_zero
  · have heq : e₁ =ᶠ[𝓝[>] (0 : ℝ)] h.e₁ := by
      filter_upwards [hsmall] with r hr
      simp [e₁, hr]
    exact (tendsto_congr' heq).2 h.e₁_zero
  · have heq : e₂ =ᶠ[𝓝[>] (0 : ℝ)] h.e₂ := by
      filter_upwards [hsmall] with r hr
      simp [e₂, hr]
    exact (tendsto_congr' heq).2 h.e₂_zero

/-- Only a local factorization on `(0,δ)` is needed for the full ball's
origin-Taylor interface. -/
noncomputable def radialOriginTaylorInterior_of_local_smooth_factor
    (p H : ℝ → ℝ) (δ R : ℝ) (hδ : 0 < δ)
    (hH : ContDiff ℝ 2 H)
    (hFactor : ∀ r : ℝ, 0 < r → r < δ → p r = r * H (r ^ 2)) :
    RadialOriginTaylorInterior p (H 0) (deriv H 0)
      (deriv (deriv H) 0 / 2) R :=
  (radialOriginTaylorInterior_of_smooth_factor p H δ hH hFactor).extendOuter hδ R

/-- Combining the local smooth factorization with the radial ODE determines
the cubic and quintic coefficients appearing in the manuscript.  The ODE is
used only at positive radii in the factorization neighborhood. -/
theorem radial_origin_coefficients_of_local_smooth_factor
    (n δ : ℝ) (p H : ℝ → ℝ)
    (hn : 3 ≤ n) (hδ : 0 < δ) (hH : ContDiff ℝ 2 H)
    (hFactor : ∀ r : ℝ, 0 < r → r < δ → p r = r * H (r ^ 2))
    (hODE : ∀ r : ℝ, 0 < r → r < δ →
      radialGLResidual n r (p r) (deriv p r)
        (deriv (deriv p) r) = 0) :
    deriv H 0 = -(H 0) / (2 * (n + 2)) ∧
      deriv (deriv H) 0 / 2 =
        (H 0) ^ 3 / (4 * (n + 4)) +
          (H 0) / (8 * (n + 2) * (n + 4)) := by
  let δ₀ : ℝ := δ / 2
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; linarith
  have hδ₀lt : δ₀ < δ := by dsimp [δ₀]; linarith
  let t : RadialOriginTaylorInterior p (H 0) (deriv H 0)
      (deriv (deriv H) 0 / 2) δ₀ :=
    radialOriginTaylorInterior_of_smooth_factor p H δ₀ hH
      (by
        intro r hr hrδ₀
        exact hFactor r hr (lt_trans hrδ₀ hδ₀lt))
  exact radial_origin_coefficients_on_localTaylor hn hδ₀
    (t.toClosed hδ₀) (by
      intro r hr hrδ₀
      exact hODE r hr (lt_of_le_of_lt hrδ₀ hδ₀lt))

end

end BrezisOP6
