import BrezisOP6.OriginExpansion

/-!
# Origin Taylor data supported only inside the finite ball

A Taylor expansion about zero is local.  This interface asks for its
differentiated formulas only at radii `0 < r < R`.  Error functions can be
defined algebraically at the outer endpoint and beyond, without claiming
that the radial ODE or any two-sided second derivative holds there.
-/

namespace BrezisOP6

open Filter Topology

noncomputable section

structure RadialOriginTaylorInterior (F : ℝ → ℝ)
    (α A B R : ℝ) where
  e₀ : ℝ → ℝ
  e₁ : ℝ → ℝ
  e₂ : ℝ → ℝ
  value : ∀ r : ℝ, 0 < r → r < R →
    F r = α * r + A * r ^ 3 + B * r ^ 5 + r ^ 5 * e₀ r
  first : ∀ r : ℝ, 0 < r → r < R →
    deriv F r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 + r ^ 4 * e₁ r
  second : ∀ r : ℝ, 0 < r → r < R →
    deriv (deriv F) r =
      6 * A * r + 20 * B * r ^ 3 + r ^ 3 * e₂ r
  e₀_zero : Tendsto e₀ (𝓝[>] (0 : ℝ)) (𝓝 0)
  e₁_zero : Tendsto e₁ (𝓝[>] (0 : ℝ)) (𝓝 0)
  e₂_zero : Tendsto e₂ (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Extend the error functions algebraically at `R`, solely to fit the
existing origin-Taylor interface.  The construction carries no outer
endpoint differentiability assertion. -/
def RadialOriginTaylorInterior.toClosed
    {F : ℝ → ℝ} {α A B R : ℝ}
    (h : RadialOriginTaylorInterior F α A B R) (hR : 0 < R) :
    RadialOriginTaylorOn F α A B R := by
  let e₀' : ℝ → ℝ := fun r =>
    if r < R then h.e₀ r else
      (F r - α * r - A * r ^ 3 - B * r ^ 5) / r ^ 5
  let e₁' : ℝ → ℝ := fun r =>
    if r < R then h.e₁ r else
      (deriv F r - α - 3 * A * r ^ 2 - 5 * B * r ^ 4) / r ^ 4
  let e₂' : ℝ → ℝ := fun r =>
    if r < R then h.e₂ r else
      (deriv (deriv F) r - 6 * A * r - 20 * B * r ^ 3) / r ^ 3
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  refine ⟨e₀', e₁', e₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr hrR
    by_cases hlt : r < R
    · change F r = α * r + A * r ^ 3 + B * r ^ 5 +
        r ^ 5 * (if r < R then h.e₀ r else _)
      simpa [hlt] using h.value r hr hlt
    · change F r = α * r + A * r ^ 3 + B * r ^ 5 +
        r ^ 5 * (if r < R then h.e₀ r else _)
      rw [if_neg hlt]
      field_simp [pow_ne_zero 5 (ne_of_gt hr)]
      ring
  · intro r hr hrR
    by_cases hlt : r < R
    · change deriv F r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * (if r < R then h.e₁ r else _)
      simpa [hlt] using h.first r hr hlt
    · change deriv F r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * (if r < R then h.e₁ r else _)
      rw [if_neg hlt]
      field_simp [pow_ne_zero 4 (ne_of_gt hr)]
      ring
  · intro r hr hrR
    by_cases hlt : r < R
    · change deriv (deriv F) r =
        6 * A * r + 20 * B * r ^ 3 +
          r ^ 3 * (if r < R then h.e₂ r else _)
      simpa [hlt] using h.second r hr hlt
    · change deriv (deriv F) r =
        6 * A * r + 20 * B * r ^ 3 +
          r ^ 3 * (if r < R then h.e₂ r else _)
      rw [if_neg hlt]
      field_simp [pow_ne_zero 3 (ne_of_gt hr)]
      ring
  · have heq : e₀' =ᶠ[𝓝[>] (0 : ℝ)] h.e₀ := by
      filter_upwards [hsmall] with r hr
      simp [e₀', hr]
    exact (tendsto_congr' heq).2 h.e₀_zero
  · have heq : e₁' =ᶠ[𝓝[>] (0 : ℝ)] h.e₁ := by
      filter_upwards [hsmall] with r hr
      simp [e₁', hr]
    exact (tendsto_congr' heq).2 h.e₁_zero
  · have heq : e₂' =ᶠ[𝓝[>] (0 : ℝ)] h.e₂ := by
      filter_upwards [hsmall] with r hr
      simp [e₂', hr]
    exact (tendsto_congr' heq).2 h.e₂_zero

def RadialOriginTaylorInterior.toGlobal
    {F : ℝ → ℝ} {α A B R : ℝ}
    (h : RadialOriginTaylorInterior F α A B R) (hR : 0 < R) :
    RadialOriginTaylor F α A B :=
  (h.toClosed hR).toGlobal hR

end

end BrezisOP6
