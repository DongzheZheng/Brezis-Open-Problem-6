import BrezisOP6.OriginExpansion
import BrezisOP6.FlowFromProfiles

/-!
# Original profile variables at the radial origin

This file transports the Taylor information from the actual radial
profiles `f` and `F` to the five variables of the contact flow. The
limits of `y`, `t`, `eta`, and `M` are derived, then the strict small-radius
sign of the original Picone residual follows from `OriginExpansion`.
-/

namespace BrezisOP6

open Filter Topology

noncomputable section

private def originRegularPart (γ A B : ℝ) (e : ℝ → ℝ) (r : ℝ) : ℝ :=
  γ + A * r ^ 2 + B * r ^ 4 + r ^ 4 * e r

private theorem originRegularPart_tendsto
    {γ A B : ℝ} {e : ℝ → ℝ}
    (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (originRegularPart γ A B e)
      (𝓝[>] (0 : ℝ)) (𝓝 γ) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hA : Tendsto (fun r : ℝ => A * r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds (x := A)).mul (hr.pow 2) using 1; simp
  have hB : Tendsto (fun r : ℝ => B * r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds (x := B)).mul (hr.pow 4) using 1; simp
  have he' : Tendsto (fun r : ℝ => r ^ 4 * e r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (hr.pow 4).mul he using 1; simp
  convert ((tendsto_const_nhds (x := γ)).add hA).add (hB.add he') using 1
  · funext r; simp [originRegularPart]; ring
  · simp

private theorem profile_eq_radius_mul_regular
    {F : ℝ → ℝ} {γ A B : ℝ}
    (h : RadialOriginTaylor F γ A B) :
    ∀ r : ℝ, 0 < r →
      F r = r * originRegularPart γ A B h.e₀ r := by
  intro r hr
  rw [h.value r hr]
  unfold originRegularPart
  ring

private theorem profile_regular_pos_eventually
    {F : ℝ → ℝ} {γ A B : ℝ}
    (hγ : 0 < γ) (h : RadialOriginTaylor F γ A B) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < originRegularPart γ A B h.e₀ r :=
  (originRegularPart_tendsto h.e₀_zero).eventually
    (eventually_gt_nhds hγ)

/-- The `t` variable has leading coefficient equal to the profile's
initial slope. -/
theorem profileT_origin_limit
    {F : ℝ → ℝ} {α A B : ℝ}
    (h : RadialOriginTaylor F α A B) :
    Tendsto (fun r => profileT F r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 α) := by
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileT F r / r ^ 2 =
        originRegularPart α A B h.e₀ r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    unfold profileT
    rw [profile_eq_radius_mul_regular h r hr]
    field_simp [ne_of_gt (show 0 < r from hr)]
  exact (tendsto_congr' heq).2
    (originRegularPart_tendsto h.e₀_zero)

/-- The logarithmic slope deficit has the universal coefficient
`1/(n+2)` forced by the cubic term of the radial equation. -/
private theorem profileY_origin_limit_of_cubic
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α)
    (h : RadialOriginTaylor F α A B)
    (hA : A = -α / (2 * (n + 2))) :
    Tendsto (fun r => profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (n + 2))) := by
  let H := originRegularPart α A B h.e₀
  let N : ℝ → ℝ := fun r =>
    -2 * A + r ^ 2 * (-4 * B + h.e₀ r - h.e₁ r)
  have hHlim : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    originRegularPart_tendsto h.e₀_zero
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hRemainder : Tendsto (fun r => -4 * B + h.e₀ r - h.e₁ r)
      (𝓝[>] (0 : ℝ)) (𝓝 (-4 * B)) := by
    simpa using ((tendsto_const_nhds (x := (-4 * B))).add
      h.e₀_zero).sub h.e₁_zero
  have hNlim : Tendsto N (𝓝[>] (0 : ℝ)) (𝓝 (-2 * A)) := by
    have ht := (tendsto_const_nhds (x := (-2 * A))).add
      ((hr.pow 2).mul hRemainder)
    simpa [N] using ht
  have hHne : ∀ᶠ r in 𝓝[>] (0 : ℝ), H r ≠ 0 :=
    (profile_regular_pos_eventually hα h).mono
      (fun r hr => ne_of_gt hr)
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileY F r / r ^ 2 = N r / H r := by
    filter_upwards [self_mem_nhdsWithin, hHne] with r hr hHr
    have hFr := profile_eq_radius_mul_regular h r hr
    have hFprime := h.first r hr
    unfold profileY
    rw [hFr, hFprime]
    dsimp [H, originRegularPart] at hHr
    dsimp [N, H, originRegularPart]
    have hHnorm : α + r ^ 2 * A + r ^ 4 * B +
        r ^ 4 * h.e₀ r ≠ 0 := by
      convert hHr using 1; ring
    field_simp [ne_of_gt (show 0 < r from hr), hHnorm]
    ring
  have hlim := (tendsto_congr' heq).2
    (hNlim.div hHlim (ne_of_gt hα))
  have hDne : n + 2 ≠ 0 := by linarith
  convert hlim using 1
  rw [hA]
  field_simp

/-- The logarithmic slope deficit for an entire profile. -/
theorem profileY_origin_limit
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α)
    (h : RadialOriginTaylor F α A B)
    (hODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (fun r => profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (n + 2))) :=
  profileY_origin_limit_of_cubic hn hα h
    (radial_origin_coefficients hn h hODE).1

/-- The same origin limit when the ODE holds only on `(0,R]`. -/
theorem profileY_origin_limit_on
    {n α A B R : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α)
    (h : RadialOriginTaylor F α A B)
    (hODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (fun r => profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (n + 2))) :=
  profileY_origin_limit_of_cubic hn hα h
    (radial_origin_coefficients_on hn hR h hODE).1

/-- Local-ODE and local-Taylor form of the slope-deficit limit. -/
theorem profileY_origin_limit_on_localTaylor
    {n α A B R : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α)
    (h : RadialOriginTaylorOn F α A B R)
    (hODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (fun r => profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (n + 2))) :=
  profileY_origin_limit_on hn hR hα (h.toGlobal hR) hODE

/-- The ratio variable tends to the quotient of the two initial slopes,
so its squared excess has a strictly positive origin limit when β>α. -/
theorem profileM_origin_limit
    {f F : ℝ → ℝ} {α β Af Bf AF BF : ℝ}
    (hα : 0 < α)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF) :
    Tendsto (profileM f F) (𝓝[>] (0 : ℝ))
      (𝓝 (β ^ 2 / α ^ 2 - 1)) := by
  let Hf := originRegularPart β Af Bf hf.e₀
  let HF := originRegularPart α AF BF hF.e₀
  have hHf : Tendsto Hf (𝓝[>] (0 : ℝ)) (𝓝 β) :=
    originRegularPart_tendsto hf.e₀_zero
  have hHF : Tendsto HF (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    originRegularPart_tendsto hF.e₀_zero
  have hHFne : ∀ᶠ r in 𝓝[>] (0 : ℝ), HF r ≠ 0 :=
    (profile_regular_pos_eventually hα hF).mono
      (fun r hr => ne_of_gt hr)
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileM f F r = (Hf r / HF r) ^ 2 - 1 := by
    filter_upwards [self_mem_nhdsWithin, hHFne] with r hr hHFr
    have hfr := profile_eq_radius_mul_regular hf r hr
    have hFr := profile_eq_radius_mul_regular hF r hr
    unfold profileM ratioM profileK
    rw [hfr, hFr]
    dsimp [Hf, HF]
    field_simp [ne_of_gt (show 0 < r from hr), hHFr]
  have hlim := (tendsto_congr' heq).2
    (((hHf.div hHF (ne_of_gt hα)).pow 2).sub_const 1)
  convert hlim using 1
  field_simp

private def originWronskianRemainder
    (α β Af Bf AF BF r ef₀ ef₁ eF₀ eF₁ : ℝ) : ℝ :=
  4 * (α * Bf - β * BF) +
    α * (ef₁ - ef₀) + β * (eF₀ - eF₁) +
    r ^ 2 *
      (2 * AF * Bf - 2 * Af * BF + 3 * Af * eF₀ + AF * ef₁ -
        Af * eF₁ - 3 * AF * ef₀) +
    r ^ 4 *
      ((5 * Bf + ef₁) * (BF + eF₀) -
        (Bf + ef₀) * (5 * BF + eF₁))

/-- With the shared cubic ratio `Af/β = AF/α` imposed by the same
radial ODE, the Wronskian starts at order five. -/
private theorem origin_wronskian_algebra
    (α β Af Bf AF BF r ef₀ ef₁ eF₀ eF₁ : ℝ)
    (hA : α * Af = β * AF) :
    (β + 3 * Af * r ^ 2 + 5 * Bf * r ^ 4 + r ^ 4 * ef₁) *
        (α + AF * r ^ 2 + BF * r ^ 4 + r ^ 4 * eF₀) -
      (β + Af * r ^ 2 + Bf * r ^ 4 + r ^ 4 * ef₀) *
        (α + 3 * AF * r ^ 2 + 5 * BF * r ^ 4 + r ^ 4 * eF₁) =
      r ^ 4 * originWronskianRemainder α β Af Bf AF BF r
        ef₀ ef₁ eF₀ eF₁ := by
  unfold originWronskianRemainder
  linear_combination 2 * r ^ 2 * hA

private theorem origin_wronskian_remainder_limit
    {α β Af Bf AF BF : ℝ}
    {ef₀ ef₁ eF₀ eF₁ : ℝ → ℝ}
    (hf₀ : Tendsto ef₀ (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hf₁ : Tendsto ef₁ (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hF₀ : Tendsto eF₀ (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hF₁ : Tendsto eF₁ (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r => originWronskianRemainder α β Af Bf AF BF r
      (ef₀ r) (ef₁ r) (eF₀ r) (eF₁ r))
      (𝓝[>] (0 : ℝ))
      (𝓝 (4 * (α * Bf - β * BF))) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have h0 : Tendsto (fun r => α * (ef₁ r - ef₀ r) +
      β * (eF₀ r - eF₁ r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert ((tendsto_const_nhds (x := α)).mul (hf₁.sub hf₀)).add
      ((tendsto_const_nhds (x := β)).mul (hF₀.sub hF₁)) using 1; simp
  have h2inner : Tendsto (fun r =>
      2 * AF * Bf - 2 * Af * BF + 3 * Af * eF₀ r +
        AF * ef₁ r - Af * eF₁ r - 3 * AF * ef₀ r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (2 * AF * Bf - 2 * Af * BF)) := by
    have h := (((tendsto_const_nhds (x :=
      2 * AF * Bf - 2 * Af * BF)).add
      ((tendsto_const_nhds (x := 3 * Af)).mul hF₀)).add
      ((tendsto_const_nhds (x := AF)).mul hf₁)).sub
      ((tendsto_const_nhds (x := Af)).mul hF₁) |>.sub
      ((tendsto_const_nhds (x := 3 * AF)).mul hf₀)
    simpa using h
  have h2 : Tendsto (fun r => r ^ 2 *
      (2 * AF * Bf - 2 * Af * BF + 3 * Af * eF₀ r +
        AF * ef₁ r - Af * eF₁ r - 3 * AF * ef₀ r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (hr.pow 2).mul h2inner using 1; simp
  have h4inner : Tendsto (fun r =>
      (5 * Bf + ef₁ r) * (BF + eF₀ r) -
        (Bf + ef₀ r) * (5 * BF + eF₁ r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h :=
      (((tendsto_const_nhds (x := 5 * Bf)).add hf₁).mul
        ((tendsto_const_nhds (x := BF)).add hF₀)).sub
      (((tendsto_const_nhds (x := Bf)).add hf₀).mul
        ((tendsto_const_nhds (x := 5 * BF)).add hF₁))
    convert h using 1
    · ring
  have h4 : Tendsto (fun r => r ^ 4 *
      ((5 * Bf + ef₁ r) * (BF + eF₀ r) -
        (Bf + ef₀ r) * (5 * BF + eF₁ r)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (hr.pow 4).mul h4inner using 1; simp
  have h := ((tendsto_const_nhds (x :=
    4 * (α * Bf - β * BF))).add h0).add h2 |>.add h4
  have hconst : 4 * (α * Bf - β * BF) + 0 + 0 + 0 =
      4 * (α * Bf - β * BF) := by ring
  rw [hconst] at h
  have hfun : (fun r => originWronskianRemainder α β Af Bf AF BF r
      (ef₀ r) (ef₁ r) (eF₀ r) (eF₁ r)) =
      (fun r => 4 * (α * Bf - β * BF) +
        (α * (ef₁ r - ef₀ r) + β * (eF₀ r - eF₁ r)) +
        r ^ 2 *
          (2 * AF * Bf - 2 * Af * BF + 3 * Af * eF₀ r +
            AF * ef₁ r - Af * eF₁ r - 3 * AF * ef₀ r) +
        r ^ 4 *
          ((5 * Bf + ef₁ r) * (BF + eF₀ r) -
            (Bf + ef₀ r) * (5 * BF + eF₁ r))) := by
    funext r
    unfold originWronskianRemainder
    ring
  rw [hfun]
  exact h

private theorem origin_wronskian_coefficient
    {n α β Bf BF : ℝ}
    (hn : 3 ≤ n) (hα : 0 < α) (hβα : α < β)
    (hfB : Bf = β ^ 3 / (4 * (n + 4)) +
      β / (8 * (n + 2) * (n + 4)))
    (hFB : BF = α ^ 3 / (4 * (n + 4)) +
      α / (8 * (n + 2) * (n + 4))) :
    4 * (α * Bf - β * BF) /
      (α ^ 2 * (β ^ 2 / α ^ 2 - 1)) = α * β / (n + 4) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hn2 : n + 2 ≠ 0 := by linarith
  have hn4 : n + 4 ≠ 0 := by linarith
  have hdiff : β ^ 2 - α ^ 2 ≠ 0 := by
    have hβ : 0 < β := lt_trans hα hβα
    have hβsq : α ^ 2 < β ^ 2 := by nlinarith
    exact ne_of_gt (sub_pos.mpr hβsq)
  rw [hfB, hFB]
  field_simp
  ring

/-- The interaction variable has the universal fourth-order origin
coefficient `αβ/(n+4)`. The fifth-order Wronskian cancellation is
proved above; the only extra regularity is differentiability of both
profiles on positive radii, needed to identify the actual derivative
of their quotient. -/
private theorem profileEta_origin_limit_of_coefficients
    {n α β Af Bf AF BF : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF)
    (hfdiff : ∀ᶠ r in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ f r)
    (hFdiff : ∀ᶠ r in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ F r)
    (hfA : Af = -β / (2 * (n + 2)))
    (hfB : Bf = β ^ 3 / (4 * (n + 4)) +
      β / (8 * (n + 2) * (n + 4)))
    (hFA : AF = -α / (2 * (n + 2)))
    (hFB : BF = α ^ 3 / (4 * (n + 4)) +
      α / (8 * (n + 2) * (n + 4))) :
    Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (α * β / (n + 4))) := by
  have hArel : α * Af = β * AF := by
    rw [hfA, hFA]
    ring
  let Hf := originRegularPart β Af Bf hf.e₀
  let HF := originRegularPart α AF BF hF.e₀
  let W : ℝ → ℝ := fun r =>
    originWronskianRemainder α β Af Bf AF BF r
      (hf.e₀ r) (hf.e₁ r) (hF.e₀ r) (hF.e₁ r)
  have hWlim : Tendsto W (𝓝[>] (0 : ℝ))
      (𝓝 (4 * (α * Bf - β * BF))) :=
    origin_wronskian_remainder_limit
      hf.e₀_zero hf.e₁_zero hF.e₀_zero hF.e₁_zero
  have hHFlim : Tendsto HF (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    originRegularPart_tendsto hF.e₀_zero
  have hMlim : Tendsto (profileM f F) (𝓝[>] (0 : ℝ))
      (𝓝 (β ^ 2 / α ^ 2 - 1)) :=
    profileM_origin_limit hα hf hF
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
  have hβ : 0 < β := lt_trans hα hβα
  have hβsq : α ^ 2 < β ^ 2 := by nlinarith
  have hM0pos : 0 < β ^ 2 / α ^ 2 - 1 := by
    have hdiv : 1 < β ^ 2 / α ^ 2 :=
      (lt_div_iff₀ hα2).2 (by simpa using hβsq)
    linarith
  have hdenpos : 0 < α ^ 2 * (β ^ 2 / α ^ 2 - 1) :=
    mul_pos hα2 hM0pos
  have hHFne : ∀ᶠ r in 𝓝[>] (0 : ℝ), HF r ≠ 0 :=
    (profile_regular_pos_eventually hα hF).mono
      (fun r hr => ne_of_gt hr)
  have hMne : ∀ᶠ r in 𝓝[>] (0 : ℝ), profileM f F r ≠ 0 :=
    (hMlim.eventually (eventually_gt_nhds hM0pos)).mono
      (fun r hr => ne_of_gt hr)
  have hdenlim : Tendsto (fun r => HF r ^ 2 * profileM f F r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (α ^ 2 * (β ^ 2 / α ^ 2 - 1))) :=
    (hHFlim.pow 2).mul hMlim
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileEta f F r / r ^ 4 =
        W r / (HF r ^ 2 * profileM f F r) := by
    filter_upwards [self_mem_nhdsWithin, hHFne, hMne,
      hfdiff, hFdiff] with r hr hHFr hMr hfder hFder
    have hrpos : 0 < r := hr
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hfr := profile_eq_radius_mul_regular hf r hrpos
    have hFr := profile_eq_radius_mul_regular hF r hrpos
    have hFne : F r ≠ 0 := by
      rw [hFr]
      exact mul_ne_zero hrne hHFr
    have hkder : deriv (profileK f F) r =
        (deriv f r * F r - f r * deriv F r) / F r ^ 2 :=
      (profileK_hasDerivAt f F r (deriv f r) (deriv F r)
        hfder.hasDerivAt hFder.hasDerivAt
        hFne).deriv
    have hW : deriv f r * F r - f r * deriv F r = r ^ 5 * W r := by
      calc
        deriv f r * F r - f r * deriv F r =
            r * ((β + 3 * Af * r ^ 2 + 5 * Bf * r ^ 4 +
                  r ^ 4 * hf.e₁ r) * HF r -
              Hf r * (α + 3 * AF * r ^ 2 + 5 * BF * r ^ 4 +
                  r ^ 4 * hF.e₁ r)) := by
          rw [hf.first r hrpos, hF.first r hrpos, hfr, hFr]
          ring
        _ = r * (r ^ 4 * W r) := by
          dsimp [Hf, HF, W, originRegularPart]
          rw [origin_wronskian_algebra α β Af Bf AF BF r
            (hf.e₀ r) (hf.e₁ r) (hF.e₀ r) (hF.e₁ r) hArel]
        _ = r ^ 5 * W r := by ring
    unfold profileEta
    rw [hkder, hW, hFr]
    dsimp [HF, originRegularPart] at hHFr ⊢
    field_simp [hrne, hHFr, hMr]
  have hquot := (tendsto_congr' heq).2
    (hWlim.div hdenlim (ne_of_gt hdenpos))
  have hcoeff := origin_wronskian_coefficient hn hα hβα hfB hFB
  simpa only [hcoeff] using hquot

/-- The fourth-order interaction asymptotic for global profile ODEs. -/
theorem profileEta_origin_limit
    {n α β Af Bf AF BF : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF)
    (hfdiff : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (α * β / (n + 4))) := by
  obtain ⟨hfA, hfB⟩ := radial_origin_coefficients hn hf hfODE
  obtain ⟨hFA, hFB⟩ := radial_origin_coefficients hn hF hFODE
  have hfdiff' : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      DifferentiableAt ℝ f r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hfdiff r hr
  have hFdiff' : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      DifferentiableAt ℝ F r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hFdiff r hr
  exact profileEta_origin_limit_of_coefficients hn hα hβα hf hF
    hfdiff' hFdiff' hfA hfB hFA hFB

/-- The fourth-order interaction asymptotic for a finite-ball profile:
both ODEs and both differentiability hypotheses need hold only on
`(0,R]`. -/
theorem profileEta_origin_limit_on
    {n α β Af Bf AF BF R : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF)
    (hfdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (α * β / (n + 4))) := by
  obtain ⟨hfA, hfB⟩ := radial_origin_coefficients_on hn hR hf hfODE
  obtain ⟨hFA, hFB⟩ := radial_origin_coefficients_on hn hR hF hFODE
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ≤ R :=
    ((eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds).mono
      (fun r hr => le_of_lt hr)
  have hfdiff' : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      DifferentiableAt ℝ f r := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    exact hfdiff r hr hrR
  have hFdiff' : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      DifferentiableAt ℝ F r := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    exact hFdiff r hr hrR
  exact profileEta_origin_limit_of_coefficients hn hα hβα hf hF
    hfdiff' hFdiff' hfA hfB hFA hFB

/-- The interaction limit with all Taylor, differentiability, and
ODE data confined to the finite positive interval. -/
theorem profileEta_origin_limit_on_localTaylor
    {n α β Af Bf AF BF R : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylorOn f β Af Bf R)
    (hF : RadialOriginTaylorOn F α AF BF R)
    (hfdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (α * β / (n + 4))) :=
  profileEta_origin_limit_on hn hR hα hβα
    (hf.toGlobal hR) (hF.toGlobal hR)
    hfdiff hFdiff hfODE hFODE

/-- The original two-profile Picone contact residual is positive on
a punctured interval at the origin. Its sign is deduced from the two
profile Taylor ansätze and their equations, not assumed. -/
theorem original_profiles_contact_pos_near_origin
    {n α β Af Bf AF BF : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF)
    (hfdiff : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < contactResidual r (profileT F r) (profileY F r)
        (profileM f F r) (profileEta f F r) := by
  exact contactResidual_pos_near_origin (by linarith : (2 : ℝ) < n)
    (profileY_origin_limit hn hα hF hFODE)
    (profileT_origin_limit hF)
    (profileEta_origin_limit hn hα hβα hf hF hfdiff hFdiff
      hfODE hFODE)
    (profileM_origin_limit hα hf hF)

/-- The actual finite-ball two-profile contact residual is positive
near zero using only ODE and differentiability data on `(0,R]`. -/
theorem original_profiles_contact_pos_near_origin_on
    {n α β Af Bf AF BF R : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylor f β Af Bf)
    (hF : RadialOriginTaylor F α AF BF)
    (hfdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < contactResidual r (profileT F r) (profileY F r)
        (profileM f F r) (profileEta f F r) := by
  exact contactResidual_pos_near_origin (by linarith : (2 : ℝ) < n)
    (profileY_origin_limit_on hn hR hα hF hFODE)
    (profileT_origin_limit hF)
    (profileEta_origin_limit_on hn hR hα hβα hf hF
      hfdiff hFdiff hfODE hFODE)
    (profileM_origin_limit hα hf hF)

/-- The finite-ball contact start with no full-axis Taylor or ODE
hypotheses. -/
theorem original_profiles_contact_pos_near_origin_on_localTaylor
    {n α β Af Bf AF BF R : ℝ} {f F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α) (hβα : α < β)
    (hf : RadialOriginTaylorOn f β Af Bf R)
    (hF : RadialOriginTaylorOn F α AF BF R)
    (hfdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ f r)
    (hFdiff : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ F r)
    (hfODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (f r) (deriv f r)
        (deriv (deriv f) r) = 0)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < contactResidual r (profileT F r) (profileY F r)
        (profileM f F r) (profileEta f F r) :=
  original_profiles_contact_pos_near_origin_on hn hR hα hβα
    (hf.toGlobal hR) (hF.toGlobal hR)
    hfdiff hFdiff hfODE hFODE

end

end BrezisOP6
