import BrezisOP6.RatioOrdering

/-!
# The initial ratio forced by a larger terminal value

The flux equation rules out an initial ratio strictly below one: before a
first upward contact with one, the positive ratio makes the flux strictly
decrease, whereas first contact would require a nonnegative ratio derivative.
The equal-initial-ratio case is separated as an explicit uniqueness input
for the regular-origin radial profile equation.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- The ratio cannot start below one and end above one.  This theorem uses
only positivity, continuity, the ratio-flux identity, and the zero initial
flux.  No uniqueness hypothesis is needed in this strict case. -/
theorem initial_ratio_not_below_one
    {k q A B : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hkcont : ContinuousOn k (Set.Icc 0 R))
    (hqcont : ContinuousOn q (Set.Icc 0 R))
    (hkdiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ k r)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k r)
    (hq0 : q 0 = 0)
    (hApos : ∀ r ∈ Set.Ioc 0 R, 0 < A r)
    (hBpos : ∀ r ∈ Set.Ioo 0 R, 0 < B r)
    (hrelation : ∀ r ∈ Set.Ioc 0 R, q r = A r * deriv k r)
    (hflux : ∀ r ∈ Set.Ioo 0 R,
      deriv q r = B r * k r * ((k r) ^ 2 - 1))
    (hterminal : 1 < k R) :
    1 ≤ k 0 := by
  by_contra hnot
  have hk0lt : k 0 < 1 := lt_of_not_ge hnot
  have hzero_exists : ∃ c ∈ Set.Icc 0 R, k c = 1 := by
    have hmem : (1 : ℝ) ∈ k '' Set.Icc 0 R :=
      intermediate_value_Icc (le_of_lt hR) hkcont
        ⟨le_of_lt hk0lt, le_of_lt hterminal⟩
    rcases hmem with ⟨c, hc, hc1⟩
    exact ⟨c, hc, hc1⟩
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
  have hkbefore : ∀ t, 0 < t → t < c → k t < 1 := by
    intro t h0t htc
    by_contra hnot
    have hkt : 1 ≤ k t := le_of_not_gt hnot
    have hmem : (1 : ℝ) ∈ k '' Set.Icc 0 t :=
      intermediate_value_Icc (le_of_lt h0t)
        (hkcont.mono (by
          intro s hs
          exact ⟨hs.1, le_trans hs.2 (le_trans (le_of_lt htc) hcI.2)⟩))
        ⟨le_of_lt hk0lt, hkt⟩
    rcases hmem with ⟨s, hs, hs1⟩
    have hsZ : s ∈ Z := by
      refine ⟨⟨hs.1, ?_⟩, ?_⟩
      · exact le_trans hs.2 (le_trans (le_of_lt htc) hcI.2)
      · simpa using hs1
    have hcs : c ≤ s := hcmin hsZ
    have hst : s ≤ t := hs.2
    linarith
  have hqanti : StrictAntiOn q (Set.Icc 0 c) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 c)
    · apply hqcont.mono
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hcI.2⟩
    · intro t ht
      have ht' : t ∈ Set.Ioo 0 c := by simpa using ht
      have htR : t ∈ Set.Ioo 0 R :=
        ⟨ht'.1, lt_of_lt_of_le ht'.2 hcI.2⟩
      rw [hflux t htR]
      have hkt0 : 0 < k t := hkpos t ⟨le_of_lt ht'.1,
        le_of_lt (lt_of_lt_of_le ht'.2 hcI.2)⟩
      have hkt1 : k t < 1 := hkbefore t ht'.1 ht'.2
      have hsq : (k t) ^ 2 - 1 < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg
        (mul_pos (hBpos t htR) hkt0) hsq
  have hqc : q c < 0 := by
    have hanti := hqanti
      (show 0 ∈ Set.Icc 0 c by exact ⟨le_rfl, le_of_lt h0c⟩)
      (show c ∈ Set.Icc 0 c by exact ⟨le_of_lt h0c, le_rfl⟩) h0c
    rw [hq0] at hanti
    exact hanti
  have hfirst : 0 ≤ deriv k c := by
    have hneg : -(deriv k c) ≤ 0 :=
      deriv_nonpos_at_first_contact h0c
        (S := fun t => -k t) (d := -(deriv k c))
        (fun t h0t htc => by
          dsimp
          rw [hc1]
          linarith [hkbefore t h0t htc])
        ((hkdiff c ⟨h0c, hcI.2⟩).hasDerivAt.neg)
    linarith
  have hcIoc : c ∈ Set.Ioc 0 R := ⟨h0c, hcI.2⟩
  have hAc : 0 < A c := hApos c hcIoc
  have hprod : 0 ≤ A c * deriv k c :=
    mul_nonneg (le_of_lt hAc) hfirst
  rw [← hrelation c hcIoc] at hprod
  linarith

/-- The equal-initial-ratio case requires the regular-origin uniqueness
input: equal initial ratios select the equilibrium ratio one.  This is the
only extra fact beyond the weighted flux needed to infer strict initial
ordering from a larger terminal value. -/
theorem initial_ratio_gt_one_of_terminal
    {k q A B : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hkcont : ContinuousOn k (Set.Icc 0 R))
    (hqcont : ContinuousOn q (Set.Icc 0 R))
    (hkdiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ k r)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k r)
    (hq0 : q 0 = 0)
    (hApos : ∀ r ∈ Set.Ioc 0 R, 0 < A r)
    (hBpos : ∀ r ∈ Set.Ioo 0 R, 0 < B r)
    (hrelation : ∀ r ∈ Set.Ioc 0 R, q r = A r * deriv k r)
    (hflux : ∀ r ∈ Set.Ioo 0 R,
      deriv q r = B r * k r * ((k r) ^ 2 - 1))
    (hterminal : 1 < k R)
    (hunique_origin : k 0 = 1 →
      ∀ r ∈ Set.Ioc 0 R, k r = 1) :
    1 < k 0 := by
  have hle := initial_ratio_not_below_one hR hkcont hqcont hkdiff
    hkpos hq0 hApos hBpos hrelation hflux hterminal
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hRone := hunique_origin heq.symm R ⟨hR, le_rfl⟩
    linarith
  · exact hlt

/-- Combining the initial-ratio result with `ratio_ordering_from_flux`
gives the full strict comparison from the terminal value. -/
theorem ratio_ordering_from_terminal
    {k q A B : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hkcont : ContinuousOn k (Set.Icc 0 R))
    (hqcont : ContinuousOn q (Set.Icc 0 R))
    (hkdiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ k r)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k r)
    (hq0 : q 0 = 0)
    (hApos : ∀ r ∈ Set.Ioc 0 R, 0 < A r)
    (hBpos : ∀ r ∈ Set.Ioo 0 R, 0 < B r)
    (hrelation : ∀ r ∈ Set.Ioc 0 R, q r = A r * deriv k r)
    (hflux : ∀ r ∈ Set.Ioo 0 R,
      deriv q r = B r * k r * ((k r) ^ 2 - 1))
    (hterminal : 1 < k R)
    (hunique_origin : k 0 = 1 →
      ∀ r ∈ Set.Ioc 0 R, k r = 1) :
    (∀ r ∈ Set.Ioc 0 R, 1 < k r) ∧
      (∀ r ∈ Set.Ioc 0 R, 0 < q r) ∧
      (∀ r ∈ Set.Ioc 0 R, 0 < deriv k r) := by
  have hk0 := initial_ratio_gt_one_of_terminal hR hkcont hqcont hkdiff
    hkpos hq0 hApos hBpos hrelation hflux hterminal hunique_origin
  exact ratio_ordering_from_flux hR hkcont hqcont hkdiff hk0 hq0
    hApos hBpos hrelation hflux

/-- A direct profile-ordering consequence of the terminal comparison and
the weighted flux hypotheses.  In the radial application, `q` is
`ratioFlux (n-1) f F`, and `A,B` are its positive weights. -/
theorem profile_gt_of_terminal_flux
    {f F k q A B : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hkcont : ContinuousOn k (Set.Icc 0 R))
    (hqcont : ContinuousOn q (Set.Icc 0 R))
    (hkdiff : ∀ r ∈ Set.Ioc 0 R, DifferentiableAt ℝ k r)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k r)
    (hq0 : q 0 = 0)
    (hApos : ∀ r ∈ Set.Ioc 0 R, 0 < A r)
    (hBpos : ∀ r ∈ Set.Ioo 0 R, 0 < B r)
    (hrelation : ∀ r ∈ Set.Ioc 0 R, q r = A r * deriv k r)
    (hflux : ∀ r ∈ Set.Ioo 0 R,
      deriv q r = B r * k r * ((k r) ^ 2 - 1))
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hquotient : ∀ r ∈ Set.Ioc 0 R, k r = f r / F r)
    (hterminal : F R < f R)
    (hunique_origin : k 0 = 1 →
      ∀ r ∈ Set.Ioc 0 R, k r = 1) :
    ∀ r ∈ Set.Ioc 0 R, F r < f r := by
  have hRI : R ∈ Set.Ioc 0 R := ⟨hR, le_rfl⟩
  have hkR : 1 < k R := by
    rw [hquotient R hRI]
    exact (lt_div_iff₀ (hFpos R hRI)).2 (by simpa using hterminal)
  obtain ⟨hkgap, _, _⟩ := ratio_ordering_from_terminal
    hR hkcont hqcont hkdiff hkpos hq0 hApos hBpos
    hrelation hflux hkR hunique_origin
  intro r hr
  have hkr : 1 < k r := hkgap r hr
  rw [hquotient r hr] at hkr
  simpa using (lt_div_iff₀ (hFpos r hr)).mp hkr

end

end BrezisOP6
