import BrezisOP6.FirstContact

/-!
# From local contact drift to global positivity

This elementary compactness lemma supplies the previously implicit
"take the first zero" step.  A continuous function positive at the left
endpoint cannot become nonpositive when its derivative is strictly positive
at every zero.  It can be applied to the Picone residual after the local
contact polynomial and the auxiliary profile bounds have been established.
-/

namespace BrezisOP6

/-- A strictly positive derivative at every zero prevents a positive
continuous function from acquiring a first contact on a compact interval. -/
theorem positive_on_Icc_of_positive_derivative_at_zeros_continuousOn
    {S : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn S (Set.Icc a b)) (hSa : 0 < S a)
    (hzeroDeriv : ∀ z, a < z → z ≤ b → S z = 0 →
      ∃ d : ℝ, HasDerivAt S d z ∧ 0 < d) :
    ∀ x ∈ Set.Icc a b, 0 < S x := by
  intro x hx
  by_contra hnot
  have hxBad : S x ≤ 0 := le_of_not_gt hnot
  let bad : Set ℝ := Set.Icc a x ∩ {z : ℝ | S z ≤ 0}
  have hcontAx : ContinuousOn S (Set.Icc a x) :=
    hcont.mono (by
      intro z hz
      exact ⟨hz.1, le_trans hz.2 hx.2⟩)
  have hclosed : IsClosed bad := by
    simpa [bad, Set.preimage] using
      (hcontAx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
  have hcompact : IsCompact bad :=
    isCompact_Icc.of_isClosed_subset hclosed (by
      intro z hz
      exact hz.1)
  have hnonempty : bad.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨⟨hx.1, le_rfl⟩, hxBad⟩
  obtain ⟨z, hz⟩ := hcompact.exists_isLeast hnonempty
  have hza : a < z := by
    by_contra h
    have hza' : z = a := le_antisymm (le_of_not_gt h) hz.1.1.1
    subst z
    exact (not_le_of_gt hSa) hz.1.2
  have hzx : z ≤ x := hz.1.1.2
  have hzb : z ≤ b := hzx.trans hx.2
  have hSz : S z = 0 := by
    by_contra hne
    have hSzle : S z ≤ 0 := hz.1.2
    have hneg : S z < 0 := lt_of_le_of_ne hSzle hne
    have hval : (0 : ℝ) ∈ Set.Icc (S z) (S a) :=
      ⟨le_of_lt hneg, le_of_lt hSa⟩
    have hcontAz : ContinuousOn S (Set.Icc a z) :=
      hcont.mono (by
        intro w hw
        exact ⟨hw.1, le_trans hw.2 hzb⟩)
    obtain ⟨w, hwI, hw0⟩ :=
      (intermediate_value_Icc' (le_of_lt hza) hcontAz) hval
    have hwlt : w < z := by
      rcases lt_or_eq_of_le hwI.2 with hlt | heq
      · exact hlt
      · subst w
        exact False.elim (hne hw0)
    have hwBad : w ∈ bad :=
      ⟨⟨hwI.1, hwI.2.trans hzx⟩, le_of_eq hw0⟩
    exact (not_le_of_gt hwlt) (hz.2 hwBad)
  have hleft : ∀ w, a < w → w < z → 0 < S w := by
    intro w haw hwz
    by_contra hnotw
    have hwBad : w ∈ bad :=
      ⟨⟨le_of_lt haw, (le_of_lt hwz).trans hzx⟩, le_of_not_gt hnotw⟩
    exact (not_le_of_gt hwz) (hz.2 hwBad)
  obtain ⟨d, hd, hdpos⟩ := hzeroDeriv z hza hzb hSz
  exact no_positive_derivative_at_first_zero hza hSz hleft hd hdpos

/-- The global-continuity version, retained for trajectories defined on
the entire logarithmic-radius line. -/
theorem positive_on_Icc_of_positive_derivative_at_zeros
    {S : ℝ → ℝ} {a b : ℝ}
    (hcont : Continuous S) (hSa : 0 < S a)
    (hzeroDeriv : ∀ z, a < z → z ≤ b → S z = 0 →
      ∃ d : ℝ, HasDerivAt S d z ∧ 0 < d) :
    ∀ x ∈ Set.Icc a b, 0 < S x :=
  positive_on_Icc_of_positive_derivative_at_zeros_continuousOn
    hcont.continuousOn hSa hzeroDeriv

end BrezisOP6
