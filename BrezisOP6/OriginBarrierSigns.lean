import BrezisOP6.OriginProfiles

/-!
# Two barrier starts supplied by the actual origin expansions

The global profile and normalized-growth barriers need one-sided signs near
the origin.  These signs follow directly from the verified profile limits.
The lower bound on the initial slope is kept visible in the profile barrier.
-/

namespace BrezisOP6

open Filter Topology

noncomputable section

/-- If the interaction variable is fourth order at the origin, it starts
strictly below the linear barrier. -/
theorem eta_lt_linear_near_origin
    {f F : ℝ → ℝ} {C : ℝ}
    (hη : Tendsto (fun r => profileEta f F r / r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 C)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      profileEta f F r < r / Real.sqrt 2 := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hquot : Tendsto (fun r => profileEta f F r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hprod := hη.mul (hr.pow 3)
    have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        profileEta f F r / r =
          (profileEta f F r / r ^ 4) * r ^ 3 := by
      filter_upwards [self_mem_nhdsWithin] with r hrpos
      have hr : 0 < r := hrpos
      field_simp [ne_of_gt hr]
    simpa using (tendsto_congr' heq).2 hprod
  have hbound : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      profileEta f F r / r < 1 / Real.sqrt 2 :=
    hquot.eventually (eventually_lt_nhds hbound)
  obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hevent
  refine ⟨δ, hδpos, ?_⟩
  intro r hr hrδ
  have h : profileEta f F r / r < 1 / Real.sqrt 2 :=
    hδ ⟨hr, hrδ⟩
  have h' := (div_lt_iff₀ hr).mp h
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h'

/-- The two-profile Taylor ansätze and ODE yield the near-origin input of
the normalized-growth barrier. -/
theorem original_profiles_eta_lt_linear_near_origin
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
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      profileEta f F r < r / Real.sqrt 2 := by
  exact eta_lt_linear_near_origin
    (profileEta_origin_limit hn hα hβα hf hF hfdiff hFdiff
      hfODE hFODE)

/-- The finite-ball version needs differentiability and the profile
equations only on `(0,R]`. -/
theorem original_profiles_eta_lt_linear_near_origin_on
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
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      profileEta f F r < r / Real.sqrt 2 := by
  exact eta_lt_linear_near_origin
    (profileEta_origin_limit_on hn hR hα hβα hf hF
      hfdiff hFdiff hfODE hFODE)

/-- The finite-ball eta barrier with all Taylor data local as well. -/
theorem original_profiles_eta_lt_linear_near_origin_on_localTaylor
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
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      profileEta f F r < r / Real.sqrt 2 :=
  original_profiles_eta_lt_linear_near_origin_on hn hR hα hβα
    (hf.toGlobal hR) (hF.toGlobal hR)
    hfdiff hFdiff hfODE hFODE

/-- The strict initial-slope inequality starts the entire-profile barrier:
`F²-y_F` has positive second-order coefficient at the origin. -/
theorem original_profile_W_pos_near_origin
    {n α A B : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hα : 0 < α)
    (hαsq : 1 / (n + 2) < α ^ 2)
    (hF : RadialOriginTaylor F α A B)
    (hFODE : ∀ r, 0 < r →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < F r ^ 2 - profileY F r := by
  have ht := profileT_origin_limit hF
  have hy := profileY_origin_limit hn hα hF hFODE
  have hscaled : Tendsto
      (fun r => (profileT F r / r ^ 2) ^ 2 -
        profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (α ^ 2 - 1 / (n + 2))) := (ht.pow 2).sub hy
  have hpos : 0 < α ^ 2 - 1 / (n + 2) := by linarith
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < (profileT F r / r ^ 2) ^ 2 -
        profileY F r / r ^ 2 :=
    hscaled.eventually (eventually_gt_nhds hpos)
  obtain ⟨ε, hεpos, hε⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hevent
  refine ⟨ε, hεpos, ?_⟩
  intro r hr hrε
  have h : 0 < (profileT F r / r ^ 2) ^ 2 -
      profileY F r / r ^ 2 := hε ⟨hr, hrε⟩
  have hsame : (profileT F r / r ^ 2) ^ 2 -
      profileY F r / r ^ 2 =
      (F r ^ 2 - profileY F r) / r ^ 2 := by
    unfold profileT
    field_simp [ne_of_gt hr]
  rw [hsame] at h
  exact (div_pos_iff_of_pos_right (pow_pos hr 2)).mp h

/-- The entire-profile amplitude barrier also has a local-ODE form;
its origin sign depends only on the cubic Taylor coefficient. -/
theorem original_profile_W_pos_near_origin_on
    {n α A B R : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α)
    (hαsq : 1 / (n + 2) < α ^ 2)
    (hF : RadialOriginTaylor F α A B)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < F r ^ 2 - profileY F r := by
  have ht := profileT_origin_limit hF
  have hy := profileY_origin_limit_on hn hR hα hF hFODE
  have hscaled : Tendsto
      (fun r => (profileT F r / r ^ 2) ^ 2 -
        profileY F r / r ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (α ^ 2 - 1 / (n + 2))) := (ht.pow 2).sub hy
  have hpos : 0 < α ^ 2 - 1 / (n + 2) := by linarith
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < (profileT F r / r ^ 2) ^ 2 -
        profileY F r / r ^ 2 :=
    hscaled.eventually (eventually_gt_nhds hpos)
  obtain ⟨ε, hεpos, hε⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hevent
  refine ⟨ε, hεpos, ?_⟩
  intro r hr hrε
  have h : 0 < (profileT F r / r ^ 2) ^ 2 -
      profileY F r / r ^ 2 := hε ⟨hr, hrε⟩
  have hsame : (profileT F r / r ^ 2) ^ 2 -
      profileY F r / r ^ 2 =
      (F r ^ 2 - profileY F r) / r ^ 2 := by
    unfold profileT
    field_simp [ne_of_gt hr]
  rw [hsame] at h
  exact (div_pos_iff_of_pos_right (pow_pos hr 2)).mp h

/-- Local-Taylor form of the finite-ball amplitude barrier start. -/
theorem original_profile_W_pos_near_origin_on_localTaylor
    {n α A B R : ℝ} {F : ℝ → ℝ}
    (hn : 3 ≤ n) (hR : 0 < R) (hα : 0 < α)
    (hαsq : 1 / (n + 2) < α ^ 2)
    (hF : RadialOriginTaylorOn F α A B R)
    (hFODE : ∀ r, 0 < r → r ≤ R →
      radialGLResidual n r (F r) (deriv F r)
        (deriv (deriv F) r) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < F r ^ 2 - profileY F r :=
  original_profile_W_pos_near_origin_on hn hR hα hαsq
    (hF.toGlobal hR) hFODE

end

end BrezisOP6
