import BrezisOP6.FirstContact

/-!
# A global sign principle for the profile flow

The first step isolates the one-dimensional fact behind the negative-branch
argument: a differentiable function whose derivative is positive at every
zero cannot move from a positive value to a negative value.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- A differentiable function which crosses every zero with positive
derivative cannot go from positive to negative on a finite interval. -/
theorem no_downcross_of_deriv_pos_at_zero
    {J : ℝ → ℝ} {u v : ℝ}
    (hJ : Differentiable ℝ J) (huv : u < v)
    (hJu : 0 < J u) (hJv : J v < 0)
    (hderiv : ∀ z ∈ Set.Icc u v, J z = 0 → 0 < deriv J z) : False := by
  have hzero_exists : ∃ z ∈ Set.Icc u v, J z = 0 := by
    have hmem : (0 : ℝ) ∈ J '' Set.Icc u v :=
      intermediate_value_Icc' (le_of_lt huv) hJ.continuous.continuousOn
        ⟨le_of_lt hJv, le_of_lt hJu⟩
    rcases hmem with ⟨z, hz, hz0⟩
    exact ⟨z, hz, hz0⟩
  let Z : Set ℝ := Set.Icc u v ∩ J ⁻¹' ({0} : Set ℝ)
  have hZcompact : IsCompact Z :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hJ.continuous)
  have hZnonempty : Z.Nonempty := by
    rcases hzero_exists with ⟨z, hz, hz0⟩
    exact ⟨z, ⟨hz, by simpa using hz0⟩⟩
  obtain ⟨z, hzZ, hzmin⟩ :=
    hZcompact.exists_isMinOn hZnonempty continuous_id.continuousOn
  have hzmem : z ∈ Set.Icc u v := hzZ.1
  have hz0 : J z = 0 := by simpa using hzZ.2
  have huz : u < z := by
    have huzle := hzmem.1
    rcases eq_or_lt_of_le huzle with heq | hlt
    · subst z
      linarith
    · exact hlt
  have hpositive : ∀ x, u < x → x < z → 0 < J x := by
    intro x hux hxz
    by_contra hnot
    have hJx : J x ≤ 0 := le_of_not_gt hnot
    have hmem : (0 : ℝ) ∈ J '' Set.Icc u x :=
      intermediate_value_Icc' (le_of_lt hux) hJ.continuous.continuousOn
        ⟨hJx, le_of_lt hJu⟩
    rcases hmem with ⟨t, ht, ht0⟩
    have htZ : t ∈ Z := by
      refine ⟨⟨ht.1, ?_⟩, ?_⟩
      · exact le_trans ht.2 (le_trans (le_of_lt hxz) hzmem.2)
      · simpa using ht0
    have hzt : z ≤ t := hzmin htZ
    have htx : t ≤ x := ht.2
    linarith
  have hzderiv : 0 < deriv J z := hderiv z hzmem hz0
  exact no_positive_derivative_at_first_zero huz hz0 hpositive
    (hJ z).hasDerivAt hzderiv

/-- A positive derivative at a zero produces positive values immediately
to its right. -/
theorem exists_pos_right_of_deriv_pos
    {J : ℝ → ℝ} {c d : ℝ}
    (hcd : c < d) (hJc : J c = 0)
    (hderiv : HasDerivAt J (deriv J c) c)
    (hpos : 0 < deriv J c) :
    ∃ u, c < u ∧ u < d ∧ 0 < J u := by
  have hlim : Filter.Tendsto (slope J c) (𝓝[>] c) (𝓝 (deriv J c)) :=
    hderiv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE c)
  have hslope : ∀ᶠ u in 𝓝[>] c, 0 < slope J c u :=
    hlim.eventually (eventually_gt_nhds hpos)
  have hbound : ∀ᶠ u in 𝓝[>] c, u < d :=
    (eventually_lt_nhds hcd).filter_mono nhdsWithin_le_nhds
  have hright : ∀ᶠ u in 𝓝[>] c, c < u := self_mem_nhdsWithin
  obtain ⟨u, hcu, hud, hs⟩ :=
    (hright.and (hbound.and hslope)).exists
  refine ⟨u, hcu, hud, ?_⟩
  rw [slope_def_field] at hs
  have hnum : 0 < J u - J c :=
    (div_pos_iff_of_pos_right (sub_pos.mpr hcu)).mp hs
  linarith

/-- A positive derivative at a zero produces negative values immediately
to its left. -/
theorem exists_neg_left_of_deriv_pos
    {J : ℝ → ℝ} {c d : ℝ}
    (hcd : c < d) (hJd : J d = 0)
    (hderiv : HasDerivAt J (deriv J d) d)
    (hpos : 0 < deriv J d) :
    ∃ v, c < v ∧ v < d ∧ J v < 0 := by
  have hlim : Filter.Tendsto (slope J d) (𝓝[<] d) (𝓝 (deriv J d)) :=
    hderiv.tendsto_slope.mono_left (nhdsLT_le_nhdsNE d)
  have hslope : ∀ᶠ v in 𝓝[<] d, 0 < slope J d v :=
    hlim.eventually (eventually_gt_nhds hpos)
  have hbound : ∀ᶠ v in 𝓝[<] d, c < v :=
    (eventually_gt_nhds hcd).filter_mono nhdsWithin_le_nhds
  have hleft : ∀ᶠ v in 𝓝[<] d, v < d := self_mem_nhdsWithin
  obtain ⟨v, hvd, hcv, hs⟩ :=
    (hleft.and (hbound.and hslope)).exists
  refine ⟨v, hcv, hvd, ?_⟩
  rw [slope_def_field] at hs
  have hnum : J v - J d < 0 := by
    rcases (div_pos_iff.mp hs) with h | h
    · linarith [h.2]
    · exact h.1
  linarith

/-- A right-sided local maximum has nonpositive derivative. -/
theorem deriv_nonpos_at_right_max
    {S : ℝ → ℝ} {r b d : ℝ}
    (hrb : r < b)
    (hright : ∀ x, r < x → x < b → S x ≤ S r)
    (hderiv : HasDerivAt S d r) : d ≤ 0 := by
  have hlim : Filter.Tendsto (slope S r) (𝓝[>] r) (𝓝 d) :=
    hderiv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE r)
  have hnear : ∀ᶠ x in 𝓝[>] r, x < b :=
    (eventually_lt_nhds hrb).filter_mono nhdsWithin_le_nhds
  have hsign : ∀ᶠ x in 𝓝[>] r, slope S r x ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin, hnear] with x hrx hxb
    have hvalue : S x - S r ≤ 0 := sub_nonpos.mpr (hright x hrx hxb)
    rw [slope_def_field]
    exact div_nonpos_of_nonpos_of_nonneg hvalue (le_of_lt (sub_pos.mpr hrx))
  exact le_of_tendsto hlim hsign

/-- A negative value between positive endpoint values belongs to a
maximal open interval of strictly negative values. -/
theorem exists_negative_component
    {W : ℝ → ℝ} {a x b : ℝ}
    (hW : Continuous W) (hax : a < x) (hxb : x < b)
    (hWa : 0 < W a) (hWx : W x < 0) (hWb : 0 < W b) :
    ∃ c d, a < c ∧ c < x ∧ x < d ∧ d < b ∧
      W c = 0 ∧ W d = 0 ∧
      ∀ t, c < t → t < d → W t < 0 := by
  have hleftzero : ∃ c ∈ Set.Icc a x, W c = 0 := by
    have hmem : (0 : ℝ) ∈ W '' Set.Icc a x :=
      intermediate_value_Icc' (le_of_lt hax) hW.continuousOn
        ⟨le_of_lt hWx, le_of_lt hWa⟩
    rcases hmem with ⟨c, hc, hc0⟩
    exact ⟨c, hc, hc0⟩
  have hrightzero : ∃ d ∈ Set.Icc x b, W d = 0 := by
    have hmem : (0 : ℝ) ∈ W '' Set.Icc x b :=
      intermediate_value_Icc (le_of_lt hxb) hW.continuousOn
        ⟨le_of_lt hWx, le_of_lt hWb⟩
    rcases hmem with ⟨d, hd, hd0⟩
    exact ⟨d, hd, hd0⟩
  let Zl : Set ℝ := Set.Icc a x ∩ W ⁻¹' ({0} : Set ℝ)
  let Zr : Set ℝ := Set.Icc x b ∩ W ⁻¹' ({0} : Set ℝ)
  have hclosed : IsClosed (W ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hW
  have hZlcompact : IsCompact Zl := isCompact_Icc.inter_right hclosed
  have hZrcompact : IsCompact Zr := isCompact_Icc.inter_right hclosed
  have hZlne : Zl.Nonempty := by
    rcases hleftzero with ⟨c, hc, hc0⟩
    exact ⟨c, ⟨hc, by simpa using hc0⟩⟩
  have hZrne : Zr.Nonempty := by
    rcases hrightzero with ⟨d, hd, hd0⟩
    exact ⟨d, ⟨hd, by simpa using hd0⟩⟩
  obtain ⟨c, hcZ, hcmax⟩ :=
    hZlcompact.exists_isMaxOn hZlne continuous_id.continuousOn
  obtain ⟨d, hdZ, hdmin⟩ :=
    hZrcompact.exists_isMinOn hZrne continuous_id.continuousOn
  have hcax : a ≤ c := hcZ.1.1
  have hcx : c ≤ x := hcZ.1.2
  have hxd : x ≤ d := hdZ.1.1
  have hdb : d ≤ b := hdZ.1.2
  have hc0 : W c = 0 := by simpa using hcZ.2
  have hd0 : W d = 0 := by simpa using hdZ.2
  have hac : a < c := by
    rcases eq_or_lt_of_le hcax with heq | hlt
    · subst c; linarith
    · exact hlt
  have hcx' : c < x := by
    rcases eq_or_lt_of_le hcx with heq | hlt
    · subst c; linarith
    · exact hlt
  have hxd' : x < d := by
    rcases eq_or_lt_of_le hxd with heq | hlt
    · subst d; linarith
    · exact hlt
  have hdb' : d < b := by
    rcases eq_or_lt_of_le hdb with heq | hlt
    · subst d; linarith
    · exact hlt
  have hleftneg : ∀ t, c < t → t < x → W t < 0 := by
    intro t hct htx
    by_contra hnot
    have hWt : 0 ≤ W t := le_of_not_gt hnot
    have hmem : (0 : ℝ) ∈ W '' Set.Icc t x :=
      intermediate_value_Icc' (le_of_lt htx) hW.continuousOn
        ⟨le_of_lt hWx, hWt⟩
    rcases hmem with ⟨s, hs, hs0⟩
    have hsZ : s ∈ Zl := by
      refine ⟨⟨le_trans hac.le (le_trans hct.le hs.1), hs.2⟩, ?_⟩
      simpa using hs0
    have hsc : s ≤ c := hcmax hsZ
    have hts : t ≤ s := hs.1
    linarith
  have hrightneg : ∀ t, x < t → t < d → W t < 0 := by
    intro t hxt htd
    by_contra hnot
    have hWt : 0 ≤ W t := le_of_not_gt hnot
    have hmem : (0 : ℝ) ∈ W '' Set.Icc x t :=
      intermediate_value_Icc (le_of_lt hxt) hW.continuousOn
        ⟨le_of_lt hWx, hWt⟩
    rcases hmem with ⟨s, hs, hs0⟩
    have hsZ : s ∈ Zr := by
      refine ⟨⟨hs.1, le_trans hs.2 (le_trans htd.le hdb)⟩, ?_⟩
      simpa using hs0
    have hds : d ≤ s := hdmin hsZ
    have hst : s ≤ t := hs.2
    linarith
  refine ⟨c, d, hac, hcx', hxd', hdb', hc0, hd0, ?_⟩
  intro t hct htd
  rcases lt_trichotomy t x with htx | heq | hxt
  · exact hleftneg t hct htx
  · simpa [heq] using hWx
  · exact hrightneg t hxt htd

/-- Finite-interval form of the profile negative-branch exclusion.  The
assumptions are precisely the two contact identities needed in the ODE
application; no special formula for `W` or `J` is used. -/
theorem nonnegative_of_profile_contact_flow
    {W J : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a)
    (hW : Differentiable ℝ W) (hJ : Differentiable ℝ J)
    (hWa : 0 < W a) (hWb : 0 < W b)
    (hflow : ∀ r ∈ Set.Icc a b, W r = 0 →
      r * deriv W r = -J r)
    (hbarrier : ∀ r ∈ Set.Icc a b, J r = 0 →
      W r ≤ 0 → 0 < deriv J r) :
    ∀ r ∈ Set.Icc a b, 0 ≤ W r := by
  intro x hx
  by_contra hnot
  have hWx : W x < 0 := lt_of_not_ge hnot
  have hax : a < x := by
    rcases eq_or_lt_of_le hx.1 with heq | hlt
    · subst x; linarith
    · exact hlt
  have hxb : x < b := by
    rcases eq_or_lt_of_le hx.2 with heq | hlt
    · subst x; linarith
    · exact hlt
  obtain ⟨c, d, hac, hcx, hxd, hdb, hc0, hd0, hneg⟩ :=
    exists_negative_component hW.continuous hax hxb hWa hWx hWb
  have hcd : c < d := lt_trans hcx hxd
  have hcI : c ∈ Set.Icc a b := ⟨le_of_lt hac, le_of_lt (lt_trans hcd hdb)⟩
  have hdI : d ∈ Set.Icc a b := ⟨le_of_lt (lt_trans hac hcd), le_of_lt hdb⟩
  have hcpos : 0 < c := lt_trans ha hac
  have hdpos : 0 < d := lt_trans hcpos hcd
  have hWderc : deriv W c ≤ 0 := by
    apply deriv_nonpos_at_right_max hcd
      (S := W) (d := deriv W c) _ (hW c).hasDerivAt
    intro t hct htd
    rw [hc0]
    exact le_of_lt (hneg t hct htd)
  have hWderd : 0 ≤ deriv W d := by
    have hnegderiv : -(deriv W d) ≤ 0 := by
      apply deriv_nonpos_at_first_contact hcd
        (S := fun t => -W t) (d := -(deriv W d))
      · intro t hct htd
        simp only [hd0, neg_zero]
        exact le_of_lt (neg_pos.mpr (hneg t hct htd))
      · exact (hW d).hasDerivAt.neg
    linarith
  have hJc : 0 ≤ J c := by
    have hp : c * deriv W c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hcpos) hWderc
    rw [hflow c hcI hc0] at hp
    linarith
  have hJd : J d ≤ 0 := by
    have hp : 0 ≤ d * deriv W d :=
      mul_nonneg (le_of_lt hdpos) hWderd
    rw [hflow d hdI hd0] at hp
    linarith
  let m : ℝ := (c + d) / 2
  have hcm : c < m := by dsimp [m]; linarith
  have hmd : m < d := by dsimp [m]; linarith
  obtain ⟨u, hcu, hum, hJu⟩ :
      ∃ u, c ≤ u ∧ u < m ∧ 0 < J u := by
    rcases eq_or_lt_of_le hJc with hcJ0 | hcJpos
    · have hJderc : 0 < deriv J c := hbarrier c hcI hcJ0.symm (le_of_eq hc0)
      obtain ⟨u, hcu, hum, hJu⟩ :=
        exists_pos_right_of_deriv_pos hcm hcJ0.symm
          (hJ c).hasDerivAt hJderc
      exact ⟨u, le_of_lt hcu, hum, hJu⟩
    · exact ⟨c, le_rfl, hcm, hcJpos⟩
  obtain ⟨v, hmv, hvd, hJv⟩ :
      ∃ v, m < v ∧ v ≤ d ∧ J v < 0 := by
    rcases eq_or_lt_of_le hJd with hdJ0 | hdJneg
    · have hJderd : 0 < deriv J d := hbarrier d hdI hdJ0 (le_of_eq hd0)
      obtain ⟨v, hmv, hvd, hJv⟩ :=
        exists_neg_left_of_deriv_pos hmd hdJ0
          (hJ d).hasDerivAt hJderd
      exact ⟨v, hmv, le_of_lt hvd, hJv⟩
    · exact ⟨d, hmd, le_rfl, hdJneg⟩
  have huv : u < v := lt_trans hum hmv
  have hWnonpos : ∀ t ∈ Set.Icc u v, W t ≤ 0 := by
    intro t ht
    have hct : c ≤ t := le_trans hcu ht.1
    have htd : t ≤ d := le_trans ht.2 hvd
    rcases eq_or_lt_of_le hct with htc | hct'
    · rw [← htc, hc0]
    · rcases lt_or_eq_of_le htd with htd' | htd'
      · exact le_of_lt (hneg t hct' htd')
      · rw [htd', hd0]
  apply no_downcross_of_deriv_pos_at_zero hJ huv hJu hJv
  intro z hz hz0
  have haz : a ≤ z := le_trans (le_of_lt hac) (le_trans hcu hz.1)
  have hzb : z ≤ b := le_trans (le_trans hz.2 hvd) (le_of_lt hdb)
  exact hbarrier z ⟨haz, hzb⟩ hz0 (hWnonpos z hz)

/-- Global form: positivity near the origin and at large radii, together
with the two contact identities, exclude every negative component. -/
theorem nonnegative_of_profile_contact_flow_global
    {W J : ℝ → ℝ}
    (hW : Differentiable ℝ W) (hJ : Differentiable ℝ J)
    (hnear : ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → 0 < W r)
    (hfar : ∃ R : ℝ, ∀ r : ℝ, R ≤ r → 0 < W r)
    (hflow : ∀ r : ℝ, 0 < r → W r = 0 →
      r * deriv W r = -J r)
    (hbarrier : ∀ r : ℝ, 0 < r → J r = 0 →
      W r ≤ 0 → 0 < deriv J r) :
    ∀ r : ℝ, 0 < r → 0 ≤ W r := by
  intro r hr
  obtain ⟨ε, hε, hsmall⟩ := hnear
  obtain ⟨R, hlarge⟩ := hfar
  let a : ℝ := min r ε / 2
  let b : ℝ := max r R + 1
  have ha : 0 < a := by
    dsimp [a]
    have hmin : 0 < min r ε := lt_min hr hε
    linarith
  have har : a < r := by
    dsimp [a]
    have hmin : min r ε ≤ r := min_le_left r ε
    linarith [ha]
  have haε : a < ε := by
    dsimp [a]
    have hmin : min r ε ≤ ε := min_le_right r ε
    linarith [ha]
  have hrb : r < b := by
    dsimp [b]
    have hmax : r ≤ max r R := le_max_left r R
    linarith
  have hRb : R ≤ b := by
    dsimp [b]
    have hmax : R ≤ max r R := le_max_right r R
    linarith
  have hWa : 0 < W a := hsmall a ha haε
  have hWb : 0 < W b := hlarge b hRb
  have hfinite := nonnegative_of_profile_contact_flow
    (W := W) (J := J) ha hW hJ hWa hWb
      (by
        intro s hs hs0
        exact hflow s (lt_of_lt_of_le ha hs.1) hs0)
      (by
        intro s hs hs0 hsnonpos
        exact hbarrier s (lt_of_lt_of_le ha hs.1) hs0 hsnonpos)
  exact hfinite r ⟨le_of_lt har, le_of_lt hrb⟩

end

end BrezisOP6
