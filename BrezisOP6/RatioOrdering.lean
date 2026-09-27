import BrezisOP6.Ratio
import BrezisOP6.FirstContact

/-!
# Ordering from the weighted ratio equation

The abstract comparison lemma uses the two pieces of the ratio ODE that
survive at the regular origin: a flux with zero initial value and a positive
source when the ratio exceeds one.  It does not assume monotonicity or the
desired ordering.  The profile corollary identifies this flux with the
weighted Wronskian from `Ratio.lean`.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- A ratio initially above one cannot return to one when its flux starts
at zero, increases wherever the ratio is above one, and is a positive
multiple of the ratio derivative.  The endpoint value at `R` is included. -/
theorem ratio_ordering_from_flux
    {k q A B : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hkcont : ContinuousOn k (Set.Icc 0 R))
    (hqcont : ContinuousOn q (Set.Icc 0 R))
    (hkdiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ k r)
    (hk0 : 1 < k 0) (hq0 : q 0 = 0)
    (hApos : ∀ r ∈ Set.Ioc 0 R, 0 < A r)
    (hBpos : ∀ r ∈ Set.Ioo 0 R, 0 < B r)
    (hrelation : ∀ r ∈ Set.Ioc 0 R, q r = A r * deriv k r)
    (hflux : ∀ r ∈ Set.Ioo 0 R,
      deriv q r = B r * k r * ((k r) ^ 2 - 1)) :
    (∀ r ∈ Set.Ioc 0 R, 1 < k r) ∧
      (∀ r ∈ Set.Ioc 0 R, 0 < q r) ∧
      (∀ r ∈ Set.Ioc 0 R, 0 < deriv k r) := by
  have hkgap : ∀ r ∈ Set.Ioc 0 R, 1 < k r := by
    intro x hx
    by_contra hnot
    have hkx : k x ≤ 1 := le_of_not_gt hnot
    have hzero_exists : ∃ c ∈ Set.Icc 0 R, k c = 1 := by
      have hmem : (1 : ℝ) ∈ k '' Set.Icc 0 x :=
        intermediate_value_Icc' (le_of_lt hx.1)
          (hkcont.mono (by
            intro t ht
            exact ⟨ht.1, le_trans ht.2 hx.2⟩))
          ⟨hkx, le_of_lt hk0⟩
      rcases hmem with ⟨c, hc, hc1⟩
      exact ⟨c, ⟨hc.1, le_trans hc.2 hx.2⟩, hc1⟩
    let Z : Set ℝ := Set.Icc 0 R ∩ k ⁻¹' ({1} : Set ℝ)
    have hZclosed : IsClosed Z :=
      hkcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hZcompact : IsCompact Z :=
      isCompact_Icc.of_isClosed_subset hZclosed (by
        intro t ht
        exact ht.1)
    have hZnonempty : Z.Nonempty := by
      rcases hzero_exists with ⟨c, hc, hc1⟩
      exact ⟨c, ⟨hc, by simpa using hc1⟩⟩
    obtain ⟨c, hcZ, hcmin⟩ :=
      hZcompact.exists_isMinOn hZnonempty continuous_id.continuousOn
    have hcI : c ∈ Set.Icc 0 R := hcZ.1
    have hc1 : k c = 1 := by simpa using hcZ.2
    have h0c : 0 < c := by
      rcases eq_or_lt_of_le hcI.1 with heq | hlt
      · subst c; linarith
      · exact hlt
    have hkbefore : ∀ t, 0 < t → t < c → 1 < k t := by
      intro t h0t htc
      by_contra hnot
      have hkt : k t ≤ 1 := le_of_not_gt hnot
      have hmem : (1 : ℝ) ∈ k '' Set.Icc 0 t :=
        intermediate_value_Icc' (le_of_lt h0t)
          (hkcont.mono (by
            intro s hs
            exact ⟨hs.1, le_trans hs.2 (le_trans (le_of_lt htc) hcI.2)⟩))
          ⟨hkt, le_of_lt hk0⟩
      rcases hmem with ⟨s, hs, hs1⟩
      have hsZ : s ∈ Z := by
        refine ⟨⟨hs.1, ?_⟩, ?_⟩
        · exact le_trans hs.2 (le_trans (le_of_lt htc) hcI.2)
        · simpa using hs1
      have hcs : c ≤ s := hcmin hsZ
      have hst : s ≤ t := hs.2
      linarith
    have hqmono : StrictMonoOn q (Set.Icc 0 c) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 c)
      · apply hqcont.mono
        intro t ht
        exact ⟨ht.1, le_trans ht.2 hcI.2⟩
      · intro t ht
        have ht' : t ∈ Set.Ioo 0 c := by simpa using ht
        have htR : t ∈ Set.Ioo 0 R :=
          ⟨ht'.1, lt_of_lt_of_le ht'.2 hcI.2⟩
        rw [hflux t htR]
        have hkt : 1 < k t := hkbefore t ht'.1 ht'.2
        have hsq : 0 < (k t) ^ 2 - 1 := by nlinarith
        exact mul_pos (mul_pos (hBpos t htR) (by linarith)) hsq
    have hqc : 0 < q c := by
      have hmono := hqmono (show 0 ∈ Set.Icc 0 c by exact ⟨le_rfl, le_of_lt h0c⟩)
        (show c ∈ Set.Icc 0 c by exact ⟨le_of_lt h0c, le_rfl⟩) h0c
      rw [hq0] at hmono
      exact hmono
    have hkcderiv : 0 < deriv k c := by
      have hcIoc : c ∈ Set.Ioc 0 R := ⟨h0c, hcI.2⟩
      have hqrelation := hrelation c hcIoc
      have hAc := hApos c hcIoc
      by_contra hn
      have hdle : deriv k c ≤ 0 := le_of_not_gt hn
      have hp : A c * deriv k c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hAc) hdle
      rw [← hqrelation] at hp
      linarith
    have hfirst : deriv k c ≤ 0 :=
      deriv_nonpos_at_first_contact h0c
        (fun t h0t htc => by rw [hc1]; exact le_of_lt (hkbefore t h0t htc))
        ((hkdiff c ⟨h0c, hcI.2⟩).hasDerivAt)
    linarith
  have hqmono : StrictMonoOn q (Set.Icc 0 R) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 R) hqcont
    intro t ht
    have ht' : t ∈ Set.Ioo 0 R := by simpa using ht
    rw [hflux t ht']
    have hkt : 1 < k t := hkgap t ⟨ht'.1, le_of_lt ht'.2⟩
    have hsq : 0 < (k t) ^ 2 - 1 := by nlinarith
    exact mul_pos (mul_pos (hBpos t ht') (by linarith)) hsq
  have hqpos : ∀ r ∈ Set.Ioc 0 R, 0 < q r := by
    intro r hr
    have hmono := hqmono (show 0 ∈ Set.Icc 0 R by exact ⟨le_rfl, le_of_lt hR⟩)
      (show r ∈ Set.Icc 0 R by exact ⟨le_of_lt hr.1, hr.2⟩) hr.1
    rwa [hq0] at hmono
  refine ⟨hkgap, hqpos, ?_⟩
  intro r hr
  have hqr : 0 < q r := hqpos r hr
  have hAr : 0 < A r := hApos r hr
  rw [hrelation r hr] at hqr
  by_contra hn
  have hdnonpos : deriv k r ≤ 0 := le_of_not_gt hn
  have : A r * deriv k r ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hAr) hdnonpos
  linarith

/-- The profile version of the comparison.  The input `k` is the
continuous extension of `f/F` to the origin; its initial value and the
continuity of the Wronskian flux are supplied by the regular-origin profile
expansion.  The pointwise second-derivative/ODE assumptions are exactly
those used by `deriv_ratioFlux` from `Ratio.lean`.  No endpoint ordering is
assumed: in particular `k R > 1` follows from the conclusion. -/
theorem ratio_ordering_profiles
    (d : ℕ) {f F k : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hfDiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ f r)
    (hFDiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ F r)
    (hkcont : ContinuousOn k (Set.Icc 0 R))
    (hfluxcont : ContinuousOn (ratioFlux (d + 1) f F) (Set.Icc 0 R))
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k =ᶠ[𝓝 r] (fun t => f t / F t))
    (hk0 : 1 < k 0)
    (hode_f : ∀ r ∈ Set.Ioo 0 R,
      ∃ f₂ : ℝ, HasDerivAt (deriv f) f₂ r ∧
        f₂ + ((d : ℝ) + 1) / r * deriv f r -
          ((d : ℝ) + 1) / r ^ 2 * f r +
          (1 - (f r) ^ 2) * f r = 0)
    (hode_F : ∀ r ∈ Set.Ioo 0 R,
      ∃ F₂ : ℝ, HasDerivAt (deriv F) F₂ r ∧
        F₂ + ((d : ℝ) + 1) / r * deriv F r -
          ((d : ℝ) + 1) / r ^ 2 * F r +
          (1 - (F r) ^ 2) * F r = 0) :
    (∀ r ∈ Set.Ioc 0 R, F r < f r) ∧
      (∀ r ∈ Set.Ioc 0 R, 0 < deriv (fun t => f t / F t) r) := by
  let A : ℝ → ℝ := fun r => r ^ (d + 1) * (F r) ^ 2
  let B : ℝ → ℝ := fun r => r ^ (d + 1) * (F r) ^ 4
  have hFne : ∀ r ∈ Set.Ioc 0 R, F r ≠ 0 :=
    fun r hr => ne_of_gt (hFpos r hr)
  have hkpoint : ∀ r ∈ Set.Ioc 0 R, k r = f r / F r :=
    fun r hr => (hkevent r hr).eq_of_nhds
  have hkdiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ k r := by
    intro r hr
    have hdiv : DifferentiableAt ℝ (fun t => f t / F t) r :=
      (hfDiff r hr).div (hFDiff r hr) (hFne r hr)
    exact hdiv.congr_of_eventuallyEq (hkevent r hr)
  have hq0 : ratioFlux (d + 1) f F 0 = 0 := by
    simp [ratioFlux]
  have hApos : ∀ r ∈ Set.Ioc 0 R, 0 < A r := by
    intro r hr
    exact mul_pos (pow_pos hr.1 _) (sq_pos_of_pos (hFpos r hr))
  have hBpos : ∀ r ∈ Set.Ioo 0 R, 0 < B r := by
    intro r hr
    exact mul_pos (pow_pos hr.1 _)
      (pow_pos (hFpos r ⟨hr.1, le_of_lt hr.2⟩) _)
  have hrelation : ∀ r ∈ Set.Ioc 0 R,
      ratioFlux (d + 1) f F r = A r * deriv k r := by
    intro r hr
    have hFlux := ratioFlux_eq_ratio (d + 1)
      (hfDiff r hr) (hFDiff r hr) (hFne r hr)
    have hderiv : deriv k r = deriv (fun t => f t / F t) r :=
      (hkevent r hr).deriv_eq
    simpa only [A, hderiv] using hFlux
  have hflux : ∀ r ∈ Set.Ioo 0 R,
      deriv (ratioFlux (d + 1) f F) r =
        B r * k r * ((k r) ^ 2 - 1) := by
    intro r hr
    obtain ⟨f₂, hdf, hodef⟩ := hode_f r hr
    obtain ⟨F₂, hdF, hodeF⟩ := hode_F r hr
    have hrIoc : r ∈ Set.Ioc 0 R := ⟨hr.1, le_of_lt hr.2⟩
    have hFlux := deriv_ratioFlux d (ne_of_gt hr.1)
      (hfDiff r hrIoc).hasDerivAt (hFDiff r hrIoc).hasDerivAt
      hdf hdF hodef hodeF
    rw [hFlux, hkpoint r hrIoc]
    dsimp [B]
    field_simp [hFne r hrIoc]
  obtain ⟨hkgap, _, hkderiv⟩ := ratio_ordering_from_flux
    hR hkcont hfluxcont hkdiff hk0 hq0 hApos hBpos hrelation hflux
  constructor
  · intro r hr
    have hkr : 1 < k r := hkgap r hr
    rw [hkpoint r hr] at hkr
    have hFr : 0 < F r := hFpos r hr
    have h := (lt_div_iff₀ hFr).mp hkr
    simpa using h
  · intro r hr
    have hkr : 0 < deriv k r := hkderiv r hr
    rw [(hkevent r hr).deriv_eq] at hkr
    exact hkr

end

end BrezisOP6
