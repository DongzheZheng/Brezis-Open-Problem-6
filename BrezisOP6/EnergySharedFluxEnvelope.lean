import BrezisOP6.EnergyTaylorFluxEnvelope

/-!
# Uniform inner flux for the second profile and the shared quotient

The second profile `F` acts on `z=u/f`.  If `0≤F≤f`, the apparent `f⁻²`
pole in the flux loses one denominator power.  The remaining envelope
has order `r^(n-2)` and tends to zero for every `n≥3`.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

theorem shared_profile_flux_scalar_bound
    (m : ℕ) (r F f dp W Cdp Cratio CW Cp : ℝ)
    (hr : 0 ≤ r) (hf : 0 < f)
    (hF0 : 0 ≤ F) (hFle : F ≤ f)
    (hW0 : 0 ≤ W) (hW : W ≤ CW)
    (hCdp : 0 ≤ Cdp) (hCratio : 0 ≤ Cratio)
    (hCp : 0 ≤ Cp)
    (hdp : |dp| ≤ Cdp)
    (hratio : |r / f| ≤ Cratio)
    (hFp : |F| ≤ Cp) :
    |r ^ (m + 2) * F * dp * (W / f ^ 2 - 1)| ≤
      r ^ (m + 1) * Cdp * Cratio * CW +
        r ^ (m + 2) * Cp * Cdp := by
  have hfne : f ≠ 0 := ne_of_gt hf
  have hpow1 : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hpow2 : 0 ≤ r ^ (m + 2) := pow_nonneg hr _
  have hratio0 : 0 ≤ r / f := div_nonneg hr hf.le
  have hFdiv0 : 0 ≤ F / f := div_nonneg hF0 hf.le
  have hFdiv1 : F / f ≤ 1 := (div_le_one hf).2 hFle
  have hreg : r ^ (m + 2) * F * dp * (W / f ^ 2 - 1) =
      r ^ (m + 1) * dp * (r / f) * (F / f) * W -
        r ^ (m + 2) * F * dp := by
    have hrpow : r ^ (m + 2) = r ^ (m + 1) * r := by
      rw [show m + 2 = m + 1 + 1 by omega, pow_succ]
    rw [hrpow]
    field_simp [hfne]
  rw [hreg]
  calc
    |r ^ (m + 1) * dp * (r / f) * (F / f) * W -
      r ^ (m + 2) * F * dp| ≤
      |r ^ (m + 1) * dp * (r / f) * (F / f) * W| +
        |r ^ (m + 2) * F * dp| := by
          simpa using abs_sub_le
            (r ^ (m + 1) * dp * (r / f) * (F / f) * W)
            0 (r ^ (m + 2) * F * dp)
    _ = r ^ (m + 1) * |dp| * (r / f) * (F / f) * W +
          r ^ (m + 2) * F * |dp| := by
      simp only [abs_mul, abs_of_nonneg hpow1,
        abs_of_nonneg hpow2, abs_of_nonneg hratio0,
        abs_of_nonneg hFdiv0, abs_of_nonneg hF0,
        abs_of_nonneg hW0]
    _ ≤ r ^ (m + 1) * Cdp * Cratio * CW +
          r ^ (m + 2) * Cp * Cdp := by
      have hratioLe : r / f ≤ Cratio := by
        simpa only [abs_of_nonneg hratio0] using hratio
      have hFLeCp : F ≤ Cp := by
        simpa only [abs_of_nonneg hF0] using hFp
      have hT : (F / f) * W ≤ W := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hFdiv1 hW0
      have hP : 0 ≤ r ^ (m + 1) * |dp| * (r / f) := by
        positivity
      have hfirst : r ^ (m + 1) * |dp| * (r / f) *
          (F / f) * W ≤
          r ^ (m + 1) * |dp| * (r / f) * W := by
        calc
          _ = (r ^ (m + 1) * |dp| * (r / f)) *
              ((F / f) * W) := by ring
          _ ≤ (r ^ (m + 1) * |dp| * (r / f)) * W :=
            mul_le_mul_of_nonneg_left hT hP
          _ = _ := by ring
      have hsecond : r ^ (m + 1) * |dp| * (r / f) * W ≤
          r ^ (m + 1) * Cdp * Cratio * CW := by
        gcongr
      have hthird : r ^ (m + 2) * F * |dp| ≤
          r ^ (m + 2) * Cp * Cdp := by
        gcongr
      exact add_le_add (hfirst.trans hsecond) hthird

/-- A positive-slope Taylor pair and a continuous numerator provide a
single vanishing envelope for every angular direction of the `F` flux
applied to `z=u/f`. -/
theorem shared_quotient_inner_flux_envelope_of_localTaylor
    (m : ℕ) (f F : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (β α Af Bf AF BF R : ℝ)
    (hR : 0 < R) (hβ : 0 < β) (hα : 0 < α)
    (hfTaylor : RadialOriginTaylorOn f β Af Bf R)
    (hFTaylor : RadialOriginTaylorOn F α AF BF R)
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (hFle : ∀ r : ℝ, 0 < r → r ≤ R →
      0 ≤ F r ∧ F r ≤ f r)
    (hu : ContinuousAt u 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧
      ∀ (ρ : ℕ → ℝ),
        (∀ k, 0 < ρ k) →
        (∀ k, ρ k < δ) →
        Tendsto ρ atTop (𝓝 0) →
        ∃ fluxBound : ℕ → ℝ,
          Tendsto fluxBound atTop (𝓝 0) ∧
            ∀ k,
              ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
                |radialBoundaryFlux m F
                  (energyRaySq (m + 3)
                    (fun x => (f ‖x‖)⁻¹ • u x) ω) (ρ k)| ≤
                  fluxBound k := by
  obtain ⟨δf, Cdf, Cratio, Cpf, hδf, hδfR,
      hCdf, hCratio, hCpf, hfBound⟩ :=
    radial_origin_local_flux_bounds_on hR hβ hfTaylor
  obtain ⟨δF, Cdp, CratioF, Cp, hδF, hδFR,
      hCdp, hCratioF, hCp, hFBound⟩ :=
    radial_origin_local_flux_bounds_on hR hα hFTaylor
  obtain ⟨δu, hδu, huBound⟩ :=
    energyRayNumerator_uniform_bound (m + 3) u hu
  let δ : ℝ := min δf (min δF δu)
  have hδ : 0 < δ := lt_min hδf (lt_min hδF hδu)
  have hδR : δ ≤ R :=
    le_trans (min_le_left _ _) hδfR
  refine ⟨δ, hδ, hδR, ?_⟩
  intro ρ hρpos hρsmall hρzero
  let envelope := quotientFluxEnvelope m u Cdp Cratio Cp ρ
  have henv : Tendsto envelope atTop (𝓝 0) := by
    have hcont : ContinuousAt
        (fun r : ℝ =>
          r ^ (m + 1) * Cdp * Cratio * (‖u 0‖ ^ 2 + 1) +
            r ^ (m + 2) * Cp * Cdp) 0 := by fun_prop
    have h := hcont.tendsto.comp hρzero
    simpa [envelope, quotientFluxEnvelope,
      zero_pow (by omega : m + 1 ≠ 0),
      zero_pow (by omega : m + 2 ≠ 0)] using h
  refine ⟨envelope, henv, ?_⟩
  intro k ω
  let r := ρ k
  have hrpos : 0 < r := hρpos k
  have hrδf : r < δf :=
    lt_of_lt_of_le (hρsmall k) (min_le_left _ _)
  have hrδF : r < δF :=
    lt_of_lt_of_le (hρsmall k)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrδu : r < δu :=
    lt_of_lt_of_le (hρsmall k)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrR : r ≤ R := le_trans (le_of_lt (hρsmall k)) hδR
  obtain ⟨hfne, _, hratio, _⟩ := hfBound r hrpos hrδf
  obtain ⟨_, hdp, _, hFp⟩ := hFBound r hrpos hrδF
  obtain ⟨hF0, hFbound⟩ := hFle r hrpos hrR
  have hfr : 0 < f r := hfpos r hrpos hrR
  have hW : ‖u (energySphereRay (m + 3) ω r)‖ ^ 2 ≤
      ‖u 0‖ ^ 2 + 1 := by
    exact (le_abs_self _).trans (huBound r hrpos hrδu ω)
  have hsq : ‖(f r)⁻¹ • u (energySphereRay (m + 3) ω r)‖ ^ 2 =
      ‖u (energySphereRay (m + 3) ω r)‖ ^ 2 / f r ^ 2 := by
    simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_eq_mul_inv]
    ring
  have hFluxEq : radialBoundaryFlux m F
      (energyRaySq (m + 3)
        (fun x => (f ‖x‖)⁻¹ • u x) ω) r =
      r ^ (m + 2) * F r * deriv F r *
        (‖u (energySphereRay (m + 3) ω r)‖ ^ 2 / f r ^ 2 - 1) := by
    simp only [radialBoundaryFlux, energyRaySq,
      energySphereRay_norm (m + 3) ω r hrpos.le, hsq]
  rw [show ρ k = r from rfl, hFluxEq]
  exact shared_profile_flux_scalar_bound m r (F r) (f r)
    (deriv F r) (‖u (energySphereRay (m + 3) ω r)‖ ^ 2)
    Cdp Cratio (‖u 0‖ ^ 2 + 1) Cp
    hrpos.le hfr hF0 hFbound (sq_nonneg _) hW
    hCdp hCratio hCp hdp hratio hFp

end

end BrezisOP6
