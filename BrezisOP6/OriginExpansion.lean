import BrezisOP6.InitialSlope
import BrezisOP6.Contact

/-!
# Origin coefficients of a regular radial profile

The regularity input is given as a differentiated Taylor ansatz with
unknown cubic and quintic coefficients and remainders tending to zero.
The radial equation determines both coefficients. In particular, the
fourth-order term of the quotient by the explicit barrier is derived,
and its strict sign gives the origin descent needed by `InitialSlope`.
-/

namespace BrezisOP6

open Filter Topology

noncomputable section

/-- The differentiated order-five Taylor ansatz at the origin. The three
remainder limits are regularity data; the coefficients `A` and `B` are
not fixed by this structure. -/
structure RadialOriginTaylor (F : ℝ → ℝ) (α A B : ℝ) where
  e₀ : ℝ → ℝ
  e₁ : ℝ → ℝ
  e₂ : ℝ → ℝ
  value : ∀ r : ℝ, 0 < r →
    F r = α * r + A * r ^ 3 + B * r ^ 5 + r ^ 5 * e₀ r
  first : ∀ r : ℝ, 0 < r →
    deriv F r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 + r ^ 4 * e₁ r
  second : ∀ r : ℝ, 0 < r →
    deriv (deriv F) r = 6 * A * r + 20 * B * r ^ 3 + r ^ 3 * e₂ r
  e₀_zero : Tendsto e₀ (𝓝[>] (0 : ℝ)) (𝓝 0)
  e₁_zero : Tendsto e₁ (𝓝[>] (0 : ℝ)) (𝓝 0)
  e₂_zero : Tendsto e₂ (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Taylor data restricted to a positive finite interval. This is the
natural input for a finite-ball profile, whose differential equation
and regularity need not be specified beyond `R`. -/
structure RadialOriginTaylorOn (F : ℝ → ℝ) (α A B R : ℝ) where
  e₀ : ℝ → ℝ
  e₁ : ℝ → ℝ
  e₂ : ℝ → ℝ
  value : ∀ r : ℝ, 0 < r → r ≤ R →
    F r = α * r + A * r ^ 3 + B * r ^ 5 + r ^ 5 * e₀ r
  first : ∀ r : ℝ, 0 < r → r ≤ R →
    deriv F r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 + r ^ 4 * e₁ r
  second : ∀ r : ℝ, 0 < r → r ≤ R →
    deriv (deriv F) r = 6 * A * r + 20 * B * r ^ 3 + r ^ 3 * e₂ r
  e₀_zero : Tendsto e₀ (𝓝[>] (0 : ℝ)) (𝓝 0)
  e₁_zero : Tendsto e₁ (𝓝[>] (0 : ℝ)) (𝓝 0)
  e₂_zero : Tendsto e₂ (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- A local Taylor ansatz supplies the existing global-error interface
by defining the error terms algebraically beyond `R`. This places no
regularity or ODE condition on the profile there. -/
def RadialOriginTaylorOn.toGlobal
    {F : ℝ → ℝ} {α A B R : ℝ}
    (h : RadialOriginTaylorOn F α A B R) (hR : 0 < R) :
    RadialOriginTaylor F α A B := by
  let e₀' : ℝ → ℝ := fun r =>
    if r ≤ R then h.e₀ r else
      (F r - α * r - A * r ^ 3 - B * r ^ 5) / r ^ 5
  let e₁' : ℝ → ℝ := fun r =>
    if r ≤ R then h.e₁ r else
      (deriv F r - α - 3 * A * r ^ 2 - 5 * B * r ^ 4) / r ^ 4
  let e₂' : ℝ → ℝ := fun r =>
    if r ≤ R then h.e₂ r else
      (deriv (deriv F) r - 6 * A * r - 20 * B * r ^ 3) / r ^ 3
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ≤ R :=
    ((eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds).mono
      (fun r hr => le_of_lt hr)
  refine ⟨e₀', e₁', e₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    by_cases hrR : r ≤ R
    · change F r = α * r + A * r ^ 3 + B * r ^ 5 +
        r ^ 5 * (if r ≤ R then h.e₀ r else _)
      simpa [hrR] using h.value r hr hrR
    · change F r = α * r + A * r ^ 3 + B * r ^ 5 +
        r ^ 5 * (if r ≤ R then h.e₀ r else _)
      rw [if_neg hrR]
      field_simp [pow_ne_zero 5 (ne_of_gt hr)]
      ring
  · intro r hr
    by_cases hrR : r ≤ R
    · change deriv F r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * (if r ≤ R then h.e₁ r else _)
      simpa [hrR] using h.first r hr hrR
    · change deriv F r = α + 3 * A * r ^ 2 + 5 * B * r ^ 4 +
        r ^ 4 * (if r ≤ R then h.e₁ r else _)
      rw [if_neg hrR]
      field_simp [pow_ne_zero 4 (ne_of_gt hr)]
      ring
  · intro r hr
    by_cases hrR : r ≤ R
    · change deriv (deriv F) r = 6 * A * r + 20 * B * r ^ 3 +
        r ^ 3 * (if r ≤ R then h.e₂ r else _)
      simpa [hrR] using h.second r hr hrR
    · change deriv (deriv F) r = 6 * A * r + 20 * B * r ^ 3 +
        r ^ 3 * (if r ≤ R then h.e₂ r else _)
      rw [if_neg hrR]
      field_simp [pow_ne_zero 3 (ne_of_gt hr)]
      ring
  · have heq : e₀' =ᶠ[𝓝[>] (0 : ℝ)] h.e₀ := by
      filter_upwards [hsmall] with r hrR
      simp [e₀', hrR]
    exact (tendsto_congr' heq).2 h.e₀_zero
  · have heq : e₁' =ᶠ[𝓝[>] (0 : ℝ)] h.e₁ := by
      filter_upwards [hsmall] with r hrR
      simp [e₁', hrR]
    exact (tendsto_congr' heq).2 h.e₁_zero
  · have heq : e₂' =ᶠ[𝓝[>] (0 : ℝ)] h.e₂ := by
      filter_upwards [hsmall] with r hrR
      simp [e₂', hrR]
    exact (tendsto_congr' heq).2 h.e₂_zero

private def originH (α A B : ℝ) (e₀ : ℝ → ℝ) (r : ℝ) : ℝ :=
  α + A * r ^ 2 + B * r ^ 4 + r ^ 4 * e₀ r

private theorem originH_tendsto {α A B : ℝ} {e₀ : ℝ → ℝ}
    (he₀ : Tendsto e₀ (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (originH α A B e₀) (𝓝[>] (0 : ℝ)) (𝓝 α) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hA : Tendsto (fun r : ℝ => A * r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds (x := A)).mul (hr.pow 2) using 1; simp
  have hB : Tendsto (fun r : ℝ => B * r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds (x := B)).mul (hr.pow 4) using 1; simp
  have he : Tendsto (fun r : ℝ => r ^ 4 * e₀ r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (hr.pow 4).mul he₀ using 1; simp
  convert ((tendsto_const_nhds (x := α)).add hA).add (hB.add he) using 1
  · funext r; simp [originH]; ring
  · simp

/-- Multiplying the singular radial equation by `r²` and inserting the
unknown Taylor coefficients leaves a polynomial identity in `r²`.
This pointwise identity is the algebraic core of coefficient extraction. -/
private theorem radial_taylor_identity
    (n α A B r e₀ e₁ e₂ : ℝ) (hr : r ≠ 0) :
    r ^ 2 * radialGLResidual n r
      (α * r + A * r ^ 3 + B * r ^ 5 + r ^ 5 * e₀)
      (α + 3 * A * r ^ 2 + 5 * B * r ^ 4 + r ^ 4 * e₁)
      (6 * A * r + 20 * B * r ^ 3 + r ^ 3 * e₂) =
    r ^ 3 * (2 * (n + 2) * A + α +
      r ^ 2 * (4 * (n + 4) * B + A -
        (α + A * r ^ 2 + B * r ^ 4 + r ^ 4 * e₀) ^ 3 +
        e₂ + (n - 1) * (e₁ - e₀)) +
      r ^ 4 * (B + e₀)) := by
  unfold radialGLResidual
  field_simp
  ring

private theorem origin_taylor_reduced_equation_at
    {n α A B r : ℝ} {F : ℝ → ℝ}
    (hTaylor : RadialOriginTaylor F α A B)
    (hr : 0 < r)
    (hODE : radialGLResidual n r (F r) (deriv F r)
      (deriv (deriv F) r) = 0) :
      2 * (n + 2) * A + α +
        r ^ 2 * (4 * (n + 4) * B + A -
          originH α A B hTaylor.e₀ r ^ 3 +
          hTaylor.e₂ r + (n - 1) * (hTaylor.e₁ r - hTaylor.e₀ r)) +
        r ^ 4 * (B + hTaylor.e₀ r) = 0 := by
  have hODEr := hODE
  rw [hTaylor.value r hr, hTaylor.first r hr,
      hTaylor.second r hr] at hODEr
  have halg := radial_taylor_identity n α A B r
    (hTaylor.e₀ r) (hTaylor.e₁ r) (hTaylor.e₂ r) (ne_of_gt hr)
  rw [hODEr] at halg
  simp only [mul_zero] at halg
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hr)
  simpa only [originH] using
    (mul_eq_zero.mp halg.symm).resolve_left hr3

/-- Coefficient extraction needs the reduced equation only in a right
neighborhood of zero. -/
private theorem radial_origin_coefficients_of_eventual_reduced
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hTaylor : RadialOriginTaylor F α A B)
    (hReduced : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      2 * (n + 2) * A + α +
        r ^ 2 * (4 * (n + 4) * B + A -
          originH α A B hTaylor.e₀ r ^ 3 +
          hTaylor.e₂ r + (n - 1) * (hTaylor.e₁ r - hTaylor.e₀ r)) +
        r ^ 4 * (B + hTaylor.e₀ r) = 0) :
    A = -α / (2 * (n + 2)) ∧
      B = α ^ 3 / (4 * (n + 4)) +
        α / (8 * (n + 2) * (n + 4)) := by
  let H := originH α A B hTaylor.e₀
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hH : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    originH_tendsto hTaylor.e₀_zero
  let E : ℝ → ℝ := fun r =>
    4 * (n + 4) * B + A - H r ^ 3 +
      hTaylor.e₂ r + (n - 1) * (hTaylor.e₁ r - hTaylor.e₀ r) +
      r ^ 2 * (B + hTaylor.e₀ r)
  have hE : Tendsto E (𝓝[>] (0 : ℝ))
      (𝓝 (4 * (n + 4) * B + A - α ^ 3)) := by
    have hconst : Tendsto (fun _ : ℝ => 4 * (n + 4) * B + A)
        (𝓝[>] (0 : ℝ)) (𝓝 (4 * (n + 4) * B + A)) :=
      tendsto_const_nhds
    have hnconst : Tendsto (fun _ : ℝ => n - 1)
        (𝓝[>] (0 : ℝ)) (𝓝 (n - 1)) := tendsto_const_nhds
    have hBconst : Tendsto (fun _ : ℝ => B)
        (𝓝[>] (0 : ℝ)) (𝓝 B) := tendsto_const_nhds
    have h := (((hconst.sub (hH.pow 3)).add hTaylor.e₂_zero).add
      (hnconst.mul (hTaylor.e₁_zero.sub hTaylor.e₀_zero))).add
      ((hr.pow 2).mul (hBconst.add hTaylor.e₀_zero))
    simpa [E] using h
  have hEq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      2 * (n + 2) * A + α + r ^ 2 * E r = 0 := by
    filter_upwards [hReduced] with r h
    dsimp [E, H]
    convert h using 1; ring
  have hLimit : Tendsto (fun r : ℝ =>
      2 * (n + 2) * A + α + r ^ 2 * E r)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (n + 2) * A + α)) := by
    convert tendsto_const_nhds.add ((hr.pow 2).mul hE) using 1; ring
  have hZero : Tendsto (fun r : ℝ =>
      2 * (n + 2) * A + α + r ^ 2 * E r)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    exact (tendsto_congr' hEq).2 tendsto_const_nhds
  have hCubic : 2 * (n + 2) * A + α = 0 :=
    tendsto_nhds_unique hLimit hZero
  have hEzero : ∀ᶠ r in 𝓝[>] (0 : ℝ), E r = 0 := by
    filter_upwards [hEq, self_mem_nhdsWithin] with r h hr₀
    rw [hCubic, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (ne_of_gt hr₀))
  have hBzero : 4 * (n + 4) * B + A - α ^ 3 = 0 := by
    have hZero' : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      exact (tendsto_congr' hEzero).2 tendsto_const_nhds
    exact tendsto_nhds_unique hE hZero'
  have hn2 : n + 2 ≠ 0 := by linarith
  have hn4 : n + 4 ≠ 0 := by linarith
  constructor
  · apply (eq_div_iff (mul_ne_zero (by norm_num) hn2)).2
    nlinarith [hCubic]
  · field_simp
    nlinarith [hCubic, hBzero]

/-- The radial ODE fixes the cubic and quintic Taylor coefficients.
No coefficient values are included in the regularity hypothesis. -/
theorem radial_origin_coefficients
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hTaylor : RadialOriginTaylor F α A B)
    (hODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    A = -α / (2 * (n + 2)) ∧
      B = α ^ 3 / (4 * (n + 4)) +
        α / (8 * (n + 2) * (n + 4)) := by
  apply radial_origin_coefficients_of_eventual_reduced hn hTaylor
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact origin_taylor_reduced_equation_at hTaylor hr (hODE r hr)

/-- The same coefficients require the radial ODE only on the finite
positive interval `(0,R]`. This is the version for a finite-ball
profile. -/
theorem radial_origin_coefficients_on
    {n α A B R : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R)
    (hTaylor : RadialOriginTaylor F α A B)
    (hODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    A = -α / (2 * (n + 2)) ∧
      B = α ^ 3 / (4 * (n + 4)) +
        α / (8 * (n + 2) * (n + 4)) := by
  apply radial_origin_coefficients_of_eventual_reduced hn hTaylor
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
  exact origin_taylor_reduced_equation_at hTaylor hr
    (hODE r hr (le_of_lt hrR))

/-- Finite-ball coefficient extraction with both ODE and Taylor data
restricted to `(0,R]`. -/
theorem radial_origin_coefficients_on_localTaylor
    {n α A B R : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R)
    (hTaylor : RadialOriginTaylorOn F α A B R)
    (hODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    A = -α / (2 * (n + 2)) ∧
      B = α ^ 3 / (4 * (n + 4)) +
        α / (8 * (n + 2) * (n + 4)) :=
  radial_origin_coefficients_on hn hR (hTaylor.toGlobal hR) hODE

/-- Rationalization removes the apparent fourth-order singularity in
the quotient expansion. The formula is purely algebraic. -/
private theorem origin_ratio_algebra
    (D α B e r s s₀ : ℝ)
    (hr : r ≠ 0) (hD : D ≠ 0) (_hs : s ≠ 0)
    (hplus : s + s₀ ≠ 0)
    (hs₀sq : s₀ ^ 2 = D)
    (hssq : s ^ 2 = D + r ^ 2) :
    (((α * r - α / (2 * D) * r ^ 3 + B * r ^ 5 + r ^ 5 * e) /
        (r / s) - α * s₀) / r ^ 4) =
      (B + e) * s -
        α * (s + 2 * s₀) / (2 * D * (s + s₀) ^ 2) := by
  have hrel : r ^ 2 = (s - s₀) * (s + s₀) := by
    nlinarith [hs₀sq, hssq]
  field_simp
  rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hrel, ← hs₀sq]
  ring

private theorem ratio_coeff_algebra
    (D α B s : ℝ) (hs : s ^ 2 = D) (hsne : s ≠ 0)
    (hDplus : D + 2 ≠ 0)
    (hB : B = α ^ 3 / (4 * (D + 2)) +
      α / (8 * D * (D + 2))) :
    B * s - 3 * α / (8 * D * s) =
      (α * s) * (D * (α * s) ^ 2 - (D + 3)) /
        (4 * (D + 2) * D ^ 2) := by
  subst D
  rw [hB]
  field_simp
  ring

/-- The quartic coefficient of `F/G` is forced by the radial ODE and
the differentiated origin Taylor ansatz. -/
theorem radial_origin_ratio_quartic
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hTaylor : RadialOriginTaylor F α A B)
    (hODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto
      (fun r => (F r / slopeBarrier n r -
        α * Real.sqrt (n + 2)) / r ^ 4)
      (𝓝[>] (0 : ℝ))
      (𝓝 (ratioQuarticCoefficient n
        (α * Real.sqrt (n + 2)))) := by
  obtain ⟨hA, hB⟩ := radial_origin_coefficients hn hTaylor hODE
  let D : ℝ := n + 2
  let s₀ : ℝ := Real.sqrt D
  let s : ℝ → ℝ := fun r => Real.sqrt (D + r ^ 2)
  have hDpos : 0 < D := by dsimp [D]; linarith
  have hs₀pos : 0 < s₀ := Real.sqrt_pos.2 hDpos
  have hs₀sq : s₀ ^ 2 = D := Real.sq_sqrt (le_of_lt hDpos)
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hsp : Tendsto s (𝓝[>] (0 : ℝ)) (𝓝 s₀) := by
    have hD : Tendsto (fun r : ℝ => D + r ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 D) := by
      convert (tendsto_const_nhds (x := D)).add (hr.pow 2) using 1; simp
    exact hD.sqrt
  have hsp_plus : Tendsto (fun r => s r + s₀)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * s₀)) := by
    convert hsp.add (tendsto_const_nhds (x := s₀)) using 1; ring
  have hden : 2 * D * (2 * s₀) ^ 2 ≠ 0 := by
    have hs₀ne : s₀ ≠ 0 := ne_of_gt hs₀pos
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hDpos))
      (pow_ne_zero 2 (mul_ne_zero (by norm_num) hs₀ne))
  have hlim : Tendsto
      (fun r => (B + hTaylor.e₀ r) * s r -
        α * (s r + 2 * s₀) /
          (2 * D * (s r + s₀) ^ 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (B * s₀ - 3 * α / (8 * D * s₀))) := by
    have hsum : Tendsto (fun r => B + hTaylor.e₀ r)
        (𝓝[>] (0 : ℝ)) (𝓝 B) := by
      simpa using (tendsto_const_nhds (x := B)).add hTaylor.e₀_zero
    have hnum : Tendsto (fun r => α * (s r + 2 * s₀))
        (𝓝[>] (0 : ℝ)) (𝓝 (3 * α * s₀)) := by
      convert (tendsto_const_nhds (x := α)).mul
        (hsp.add (tendsto_const_nhds (x := 2 * s₀))) using 1; ring
    have hden' : Tendsto (fun r => 2 * D * (s r + s₀) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * D * (2 * s₀) ^ 2)) := by
      convert (tendsto_const_nhds (x := 2 * D)).mul
        (hsp_plus.pow 2) using 1
    have h := (hsum.mul hsp).sub (hnum.div hden' hden)
    have hval : 3 * α * s₀ / (2 * D * (2 * s₀) ^ 2) =
        3 * α / (8 * D * s₀) := by
      field_simp
      ring
    simpa only [hval] using h
  have hEq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (F r / slopeBarrier n r - α * Real.sqrt (n + 2)) / r ^ 4 =
        (B + hTaylor.e₀ r) * s r -
          α * (s r + 2 * s₀) /
            (2 * D * (s r + s₀) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with r hr₀
    have hD_r : 0 < D + r ^ 2 := by nlinarith [sq_nonneg r]
    have hspos : 0 < s r := Real.sqrt_pos.2 hD_r
    have hplus : s r + s₀ ≠ 0 := by positivity
    have hsquare : s r ^ 2 = D + r ^ 2 := Real.sq_sqrt (le_of_lt hD_r)
    have hFr : F r = α * r - α / (2 * D) * r ^ 3 +
        B * r ^ 5 + r ^ 5 * hTaylor.e₀ r := by
      calc
        F r = α * r + A * r ^ 3 + B * r ^ 5 +
            r ^ 5 * hTaylor.e₀ r := hTaylor.value r hr₀
        _ = _ := by
          have hA' : A = -α / (2 * D) := by simpa [D] using hA
          linear_combination (r ^ 3) * hA'
    rw [hFr]
    have hsEq : slopeBarrier n r = r / s r := by
      dsimp [slopeBarrier, s, D]
      congr 1
      ring
    rw [hsEq]
    change (((α * r - α / (2 * D) * r ^ 3 + B * r ^ 5 +
      r ^ 5 * hTaylor.e₀ r) / (r / s r) - α * s₀) / r ^ 4) = _
    exact origin_ratio_algebra D α B (hTaylor.e₀ r) r (s r) s₀
      (ne_of_gt hr₀) (ne_of_gt hDpos) (ne_of_gt hspos)
      hplus hs₀sq hsquare
  have hCoeff : B * s₀ - 3 * α / (8 * D * s₀) =
      ratioQuarticCoefficient n (α * Real.sqrt (n + 2)) := by
    have hB' : B = α ^ 3 / (4 * (D + 2)) +
        α / (8 * D * (D + 2)) := by
      have hN4 : D + 2 = n + 4 := by dsimp [D]; ring
      rw [hN4]
      simpa only [D] using hB
    have hDplus : D + 2 ≠ 0 := by
      apply ne_of_gt
      linarith
    have h := ratio_coeff_algebra D α B s₀ hs₀sq
      (ne_of_gt hs₀pos) hDplus hB'
    convert h using 1; simp [ratioQuarticCoefficient, D, s₀]; ring
  exact hCoeff ▸ (tendsto_congr' hEq).2 hlim

/-- The Taylor ansatz itself gives the zero-radius quotient limit. -/
theorem radial_origin_ratio_limit
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hTaylor : RadialOriginTaylor F α A B) :
    Tendsto (fun r => F r / slopeBarrier n r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (α * Real.sqrt (n + 2))) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hD : Tendsto (fun r : ℝ => n + 2 + r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (n + 2)) := by
    convert (tendsto_const_nhds (x := n + 2)).add (hr.pow 2) using 1; simp
  have hH : Tendsto (originH α A B hTaylor.e₀)
      (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    originH_tendsto hTaylor.e₀_zero
  have hprod := hH.mul hD.sqrt
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      F r / slopeBarrier n r =
        originH α A B hTaylor.e₀ r * Real.sqrt (n + 2 + r ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with r hr₀
    have hval := hTaylor.value r hr₀
    have hDpos : 0 < n + 2 + r ^ 2 := by
      nlinarith [sq_nonneg r]
    have hsne : Real.sqrt (n + 2 + r ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hDpos)
    rw [hval]
    dsimp [slopeBarrier, originH]
    have hsEq : Real.sqrt (r ^ 2 + n + 2) =
        Real.sqrt (n + 2 + r ^ 2) := by congr 1; ring
    rw [hsEq]
    have hrne : r ≠ 0 := ne_of_gt (show 0 < r from hr₀)
    field_simp [hrne, hsne]
  have h : Tendsto (fun r =>
      originH α A B hTaylor.e₀ r * Real.sqrt (n + 2 + r ^ 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (α * Real.sqrt (n + 2))) := by
    simpa using hprod
  exact (tendsto_congr' heq).2 h

/-- When the initial slope is at or below the proposed threshold, the
radial equation forces the quotient to drop strictly below its origin
limit at a positive radius. -/
theorem radial_origin_ratio_descent
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α)
    (hsmall : α ^ 2 ≤ 1 / (n + 2))
    (hTaylor : RadialOriginTaylor F α A B)
    (hODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      F r₀ / slopeBarrier n r₀ < α * Real.sqrt (n + 2) := by
  have hDpos : 0 < n + 2 := by linarith
  have hspos : 0 < Real.sqrt (n + 2) := Real.sqrt_pos.2 hDpos
  have hLpos : 0 < α * Real.sqrt (n + 2) := mul_pos hα hspos
  have hLsq : (α * Real.sqrt (n + 2)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hDpos)]
    exact (le_div_iff₀ hDpos).mp hsmall
  have hLle : α * Real.sqrt (n + 2) ≤ 1 := by nlinarith
  exact exists_origin_descent_of_quartic_limit
    (ratioQuarticCoefficient_neg hn hLpos hLle)
    (radial_origin_ratio_quartic hn hTaylor hODE)

/-- The complete initial-slope bound under an explicit differentiated
order-five origin Taylor regularity hypothesis. The ODE, rather than a
postulated quartic coefficient or minimum, drives the strict barrier. -/
theorem entire_profile_initial_slope_gt_of_taylor
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α)
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hFC2 : ContDiffOn ℝ 2 F (Set.Ioi 0))
    (hTaylor : RadialOriginTaylor F α A B)
    (hinfty : Tendsto (fun r => F r / slopeBarrier n r)
      atTop (𝓝 (1 : ℝ)))
    (hODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    1 / (n + 2) < α ^ 2 := by
  exact entire_profile_initial_slope_gt hn hα hFpos hFC2
    (radial_origin_ratio_limit hn hTaylor) hinfty
    (radial_origin_ratio_quartic hn hTaylor hODE) hODE

/-- Exact weighted scaling of the Picone contact residual. At the
origin `t=O(r²)` and `eta=O(r⁴)`, so only the `r²-4y` terms survive
after division by `r²`. -/
private theorem contactResidual_origin_scaling
    (r t y M eta : ℝ) (hr : r ≠ 0) :
    contactResidual r t y M eta / r ^ 2 =
      1 + M * (t / r ^ 2) ^ 2 * r ^ 2 -
        4 * (y / r ^ 2) -
        2 * (y / r ^ 2) ^ 2 * r ^ 2 -
        (eta / r ^ 4) ^ 2 * r ^ 6 := by
  unfold contactResidual
  field_simp

/-- Equation (5.4)'s leading origin coefficient from independently
tracked limits of all five flow variables. The auxiliary limits for
`t`, `eta`, and `M` may be supplied by their Taylor/flow analysis; the
coefficient of the limit depends only on `y/r²`. -/
theorem contactResidual_origin_limit
    {n α η₀ M₀ : ℝ} {t y M eta : ℝ → ℝ}
    (hn : 2 < n)
    (hy : Tendsto (fun r => y r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (n + 2))))
    (ht : Tendsto (fun r => t r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 α))
    (heta : Tendsto (fun r => eta r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 η₀))
    (hM : Tendsto M (𝓝[>] (0 : ℝ)) (𝓝 M₀)) :
    Tendsto (fun r => contactResidual r (t r) (y r) (M r)
      (eta r) / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((n - 2) / (n + 2))) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hTterm : Tendsto
      (fun r => M r * (t r / r ^ 2) ^ 2 * r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (hM.mul (ht.pow 2)).mul (hr.pow 2) using 1; simp
  have hYterm : Tendsto (fun r => 4 * (y r / r ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 * (1 / (n + 2)))) := by
    exact (tendsto_const_nhds (x := (4 : ℝ))).mul hy
  have hY2term : Tendsto
      (fun r => 2 * (y r / r ^ 2) ^ 2 * r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert ((tendsto_const_nhds (x := (2 : ℝ))).mul
      (hy.pow 2)).mul (hr.pow 2) using 1; simp
  have hEterm : Tendsto
      (fun r => (eta r / r ^ 4) ^ 2 * r ^ 6)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (heta.pow 2).mul (hr.pow 6) using 1; simp
  have hcomb : Tendsto
      (fun r => 1 + M r * (t r / r ^ 2) ^ 2 * r ^ 2 -
        4 * (y r / r ^ 2) -
        2 * (y r / r ^ 2) ^ 2 * r ^ 2 -
        (eta r / r ^ 4) ^ 2 * r ^ 6)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - 4 / (n + 2))) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add hTterm).sub
      hYterm).sub hY2term |>.sub hEterm
    convert h using 1; ring
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      contactResidual r (t r) (y r) (M r) (eta r) / r ^ 2 =
        1 + M r * (t r / r ^ 2) ^ 2 * r ^ 2 -
          4 * (y r / r ^ 2) -
          2 * (y r / r ^ 2) ^ 2 * r ^ 2 -
          (eta r / r ^ 4) ^ 2 * r ^ 6 := by
    filter_upwards [self_mem_nhdsWithin] with r hr₀
    exact contactResidual_origin_scaling r (t r) (y r) (M r) (eta r)
      (ne_of_gt (show 0 < r from hr₀))
  have hlim := (tendsto_congr' heq).2 hcomb
  convert hlim using 1
  have hD : n + 2 ≠ 0 := by linarith
  field_simp
  ring

/-- The strict `n-2` gain is an actual punctured-neighborhood sign,
not merely a formal leading coefficient. This supplies the initial
left positivity used by the first-contact argument. -/
theorem contactResidual_pos_near_origin
    {n α η₀ M₀ : ℝ} {t y M eta : ℝ → ℝ}
    (hn : 2 < n)
    (hy : Tendsto (fun r => y r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (n + 2))))
    (ht : Tendsto (fun r => t r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 α))
    (heta : Tendsto (fun r => eta r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 η₀))
    (hM : Tendsto M (𝓝[>] (0 : ℝ)) (𝓝 M₀)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < contactResidual r (t r) (y r) (M r) (eta r) := by
  have hDpos : 0 < n + 2 := by linarith
  have hLpos : 0 < (n - 2) / (n + 2) :=
    div_pos (by linarith) hDpos
  have hnear : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < contactResidual r (t r) (y r) (M r) (eta r) := by
    filter_upwards [self_mem_nhdsWithin,
      (contactResidual_origin_limit hn hy ht heta hM).eventually
        (eventually_gt_nhds hLpos)] with r hr₀ hquot
    have hr2 : 0 < r ^ 2 := pow_pos (show 0 < r from hr₀) 2
    have h := (lt_div_iff₀ hr2).mp hquot
    simpa using h
  obtain ⟨ε, hε, hinterval⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hnear
  exact ⟨ε, hε, fun r hr hrε => hinterval ⟨hr, hrε⟩⟩

end

end BrezisOP6
