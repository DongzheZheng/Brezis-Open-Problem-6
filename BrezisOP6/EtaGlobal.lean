import BrezisOP6.EtaFlowFromProfiles
import BrezisOP6.GlobalContact

/-!
# The global normalized-growth barrier

The origin estimate starts the barrier strictly below the line
`r / sqrt 2`.  Compactness extracts a first contact from any putative
failure.  At every such contact the actual `η` flow points strictly
downward, while first-contact calculus requires an upward derivative.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- The strict `η < r / √2` barrier on the entire positive interval.
The near-origin assumption can be supplied by the profile expansion
`η = O(r⁴)`; all other hypotheses are pointwise flow data. -/
theorem eta_barrier_on_positive_interval
    {η F y k : ℝ → ℝ} {ν R : ℝ}
    (hR : 0 < R) (hν : 2 ≤ ν)
    (hηcont : ContinuousOn η (Set.Icc 0 R))
    (hnear : ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ → η r < r / Real.sqrt 2)
    (hηdiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ η r)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hFlt : ∀ r ∈ Set.Ioc 0 R, F r < 1)
    (hkpos : ∀ r ∈ Set.Ioc 0 R, 0 < k r)
    (hylt : ∀ r ∈ Set.Ioc 0 R, y r < 1)
    (hflow : ∀ r ∈ Set.Ioc 0 R,
      r * deriv η r =
        k r * (r * F r) ^ 2 -
          (ν - 2 * y r) * η r - 2 * k r * (η r) ^ 2) :
    ∀ r ∈ Set.Ioc 0 R, η r < r / Real.sqrt 2 := by
  obtain ⟨δ, hδ, hsmall⟩ := hnear
  let a : ℝ := min δ R / 2
  have ha : 0 < a := by
    dsimp [a]
    have hmin : 0 < min δ R := lt_min hδ hR
    linarith
  have haδ : a < δ := by
    dsimp [a]
    have hmin : min δ R ≤ δ := min_le_left δ R
    linarith [ha]
  have haR : a < R := by
    dsimp [a]
    have hmin : min δ R ≤ R := min_le_right δ R
    linarith [ha]
  let S : ℝ → ℝ := fun r => r / Real.sqrt 2 - η r
  have hScont : ContinuousOn S (Set.Icc 0 R) :=
    (continuous_id.div_const (Real.sqrt 2)).continuousOn.sub hηcont
  have hSa : 0 < S a := by
    dsimp [S]
    linarith [hsmall a ha haδ]
  have hSpos : ∀ r ∈ Set.Icc a R, 0 < S r := by
    apply positive_on_Icc_of_positive_derivative_at_zeros_continuousOn
      (hScont.mono (by
        intro z hz
        exact ⟨le_of_lt (lt_of_lt_of_le ha hz.1), hz.2⟩)) hSa
    intro z haz hzR hSz
    have hzpos : 0 < z := lt_trans ha haz
    have hzI : z ∈ Set.Ioc 0 R := ⟨hzpos, hzR⟩
    have hcontact : η z = z / Real.sqrt 2 := by
      dsimp [S] at hSz
      linarith
    have hneg : z * deriv η z < 0 :=
      eta_flow_negative_at_barrier hzpos (hkpos z hzI)
        (hFpos z hzI) (hFlt z hzI) (hylt z hzI) hν
        rfl hcontact (hflow z hzI)
    have hηderivneg : deriv η z < 0 := by
      by_contra hn
      have hnonneg : 0 ≤ deriv η z := le_of_not_gt hn
      have hp : 0 ≤ z * deriv η z :=
        mul_nonneg (le_of_lt hzpos) hnonneg
      linarith
    have hrootpos : 0 < Real.sqrt 2 :=
      Real.sqrt_pos.2 (by norm_num)
    have hSderiv : HasDerivAt S
        (1 / Real.sqrt 2 - deriv η z) z := by
      dsimp [S]
      exact ((hasDerivAt_id z).div_const (Real.sqrt 2)).sub
        (hηdiff z hzI).hasDerivAt
    refine ⟨1 / Real.sqrt 2 - deriv η z, hSderiv, ?_⟩
    have hbarrierSlope : 0 < (1 : ℝ) / Real.sqrt 2 :=
      div_pos (by norm_num) hrootpos
    linarith
  intro r hr
  by_cases har : a ≤ r
  · have hSr : 0 < S r := hSpos r ⟨har, hr.2⟩
    dsimp [S] at hSr
    linarith
  · exact hsmall r hr.1 (lt_trans (lt_of_not_ge har) haδ)

/-- Profile-level form.  The local ODE data are passed through
`profileEta_barrier_inputs`, so the contact flow is derived from the
original pair of radial profile equations. -/
theorem profile_eta_barrier_on_positive_interval
    (d : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hηcont : ContinuousOn (profileEta f F) (Set.Icc 0 R))
    (hnear : ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ →
        profileEta f F r < r / Real.sqrt 2)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hFlt : ∀ r ∈ Set.Ioc 0 R, F r < 1)
    (hkpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileK f F r)
    (hMpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileM f F r)
    (hylt : ∀ r ∈ Set.Ioc 0 R, profileY F r < 1)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hprofiles : ∀ r ∈ Set.Ioc 0 R,
      ∃ f₁ F₁ f₂ F₂ : ℝ,
        HasDerivAt f f₁ r ∧ HasDerivAt F F₁ r ∧
        HasDerivAt (deriv f) f₂ r ∧
        HasDerivAt (deriv F) F₂ r ∧
        radialODEAt ((d : ℝ) + 3) r (f r) f₁ f₂ ∧
        radialODEAt ((d : ℝ) + 3) r (F r) F₁ F₂) :
    ∀ r ∈ Set.Ioc 0 R,
      profileEta f F r < r / Real.sqrt 2 := by
  have hinputs : ∀ r ∈ Set.Ioc 0 R,
      ∃ η₁ : ℝ,
        HasDerivAt (profileEta f F) η₁ r ∧
        r * η₁ =
          profileK f F r * profileT F r ^ 2 -
          (((d : ℝ) + 3) - 2 * profileY F r) *
            profileEta f F r -
          2 * profileK f F r * profileEta f F r ^ 2 := by
    intro r hr
    obtain ⟨f₁, F₁, f₂, F₂, hf, hF, hdf, hdF, hodef, hodeF⟩ :=
      hprofiles r hr
    exact profileEta_barrier_inputs d f F r f₁ F₁ f₂ F₂
      hr.1 (hFpos r hr) (hMpos r hr) hfDiff hFDiff
      hf hF hdf hdF hodef hodeF
  have hν : (2 : ℝ) ≤ (d : ℝ) + 3 := by
    have hdnonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  apply eta_barrier_on_positive_interval hR hν hηcont hnear
  · intro r hr
    obtain ⟨η₁, hder, _⟩ := hinputs r hr
    exact hder.differentiableAt
  · exact hFpos
  · exact hFlt
  · exact hkpos
  · exact hylt
  · intro r hr
    obtain ⟨η₁, hder, hflow⟩ := hinputs r hr
    rw [hder.deriv]
    simpa only [profileT] using hflow

end

end BrezisOP6
