import BrezisOP6.OriginRatioLocalProfile
import BrezisOP6.OriginTaylorInterior
import BrezisOP6.OriginFluxFactor

/-!
# Elimination of the singular initial-value uniqueness input near zero

The initial Taylor limit gives `F(r)≤Lr` at small radius, while continuity
of the regular-origin ratio with `k₀(0)=1` bounds that ratio by two.  A
small interval can then be chosen so the already-verified two-MVT
contraction applies to the actual profile Wronskian.  Positive-radius
continuation is a separate, nonsingular ODE uniqueness step.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

theorem profile_ratio_one_on_some_origin_interval
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (R α AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) R))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkzero : k₀ 0 = 1)
    (hfluxcont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r)) :
    ∃ a : ℝ, 0 < a ∧ a < R ∧
      ∀ r ∈ Icc (0 : ℝ) a, k₀ r = 1 := by
  let c : ℝ := α / 2
  let L : ℝ := α + 1
  let C : ℝ := L ^ 4 / c ^ 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (pow_nonneg hL _) (sq_nonneg c)
  have hCL : L ^ 4 ≤ C * c ^ 2 := by
    dsimp [C]
    field_simp [ne_of_gt hc]
    exact le_rfl
  have hFLim := profile_div_radius_origin_limit
    (hFTaylor.toGlobal hR)
  have hFEvent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c < F r / r ∧ F r / r < L := by
    have hlow : ∀ᶠ r in 𝓝[>] (0 : ℝ), c < F r / r :=
      hFLim.eventually (eventually_gt_nhds (by dsimp [c]; linarith))
    have hhigh : ∀ᶠ r in 𝓝[>] (0 : ℝ), F r / r < L :=
      hFLim.eventually (eventually_lt_nhds (by dsimp [L]; linarith))
    filter_upwards [hlow, hhigh] with r hr0 hrL
    exact ⟨hr0, hrL⟩
  obtain ⟨δF, hδF, hFsmall⟩ :=
    (nhdsGT_basis (0 : ℝ)).mem_iff.mp hFEvent
  have hwithin : (𝓝[>] (0 : ℝ)) ≤
      (𝓝[Icc (0 : ℝ) R] (0 : ℝ)) :=
    nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT hR)
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) R :=
    ⟨le_rfl, hR.le⟩
  have hKLim : Tendsto k₀ (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [hkzero] using
      (hkcont.continuousWithinAt h0mem).tendsto.mono_left hwithin
  have hKEvent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 ≤ k₀ r ∧ k₀ r ≤ 2 := by
    have hlow : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < k₀ r :=
      hKLim.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    have hhigh : ∀ᶠ r in 𝓝[>] (0 : ℝ), k₀ r < 2 :=
      hKLim.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [hlow, hhigh] with r hr0 hr2
    exact ⟨hr0.le, hr2.le⟩
  obtain ⟨δK, hδK, hKsmall⟩ :=
    (nhdsGT_basis (0 : ℝ)).mem_iff.mp hKEvent
  have hCLim : Tendsto (fun r : ℝ => 6 * C * r ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun r : ℝ => 6 * C * r ^ 4) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hCEvent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      6 * C * r ^ 4 < 1 :=
    hCLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨δC, hδC, hCsmall⟩ :=
    (nhdsGT_basis (0 : ℝ)).mem_iff.mp hCEvent
  let δ : ℝ := min R (min δF (min δK δC))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hR (lt_min hδF (lt_min hδK hδC))
  let a : ℝ := δ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have haδ : a < δ := by dsimp [a]; linarith
  have haR : a < R :=
    lt_of_lt_of_le haδ (by
      dsimp [δ]
      exact min_le_left R (min δF (min δK δC)))
  have haF : a < δF :=
    lt_of_lt_of_le haδ (by
      dsimp [δ]
      exact le_trans (min_le_right R (min δF (min δK δC)))
        (min_le_left δF (min δK δC)))
  have haK : a < δK :=
    lt_of_lt_of_le haδ (by
      dsimp [δ]
      exact le_trans (min_le_right R (min δF (min δK δC)))
        (le_trans (min_le_right δF (min δK δC))
          (min_le_left δK δC)))
  have haC : a < δC :=
    lt_of_lt_of_le haδ (by
      dsimp [δ]
      exact le_trans (min_le_right R (min δF (min δK δC)))
        (le_trans (min_le_right δF (min δK δC))
          (min_le_right δK δC)))
  have hFlower : ∀ r ∈ Ioo (0 : ℝ) a, c * r ≤ F r := by
    intro r hr
    have hquot : c < F r / r :=
      (hFsmall ⟨hr.1, lt_trans hr.2 haF⟩).1
    exact ((lt_div_iff₀ hr.1).mp hquot).le
  have hFupper : ∀ r ∈ Ioo (0 : ℝ) a, F r ≤ L * r := by
    intro r hr
    have hquot : F r / r < L :=
      (hFsmall ⟨hr.1, lt_trans hr.2 haF⟩).2
    exact (div_lt_iff₀ hr.1).mp hquot |>.le
  have hkbounded : ∀ r ∈ Icc (0 : ℝ) a,
      0 ≤ k₀ r ∧ k₀ r ≤ 2 := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hzero | hpos
    · rw [← hzero, hkzero]
      norm_num
    · exact hKsmall ⟨hpos, lt_of_le_of_lt hr.2 haK⟩
  have hsmall : 6 * C * a ^ 4 < 1 :=
    hCsmall ⟨ha, haC⟩
  have hsubClosed (r : ℝ) (hr : r ∈ Icc (0 : ℝ) a) :
      r ∈ Icc (0 : ℝ) R :=
    ⟨hr.1, hr.2.trans haR.le⟩
  have hsubOpen (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) a) :
      r ∈ Ioo (0 : ℝ) R :=
    ⟨hr.1, lt_trans hr.2 haR⟩
  have hsubHalfOpen (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) a) :
      r ∈ Ioc (0 : ℝ) R :=
    ⟨hr.1, hr.2.trans haR.le⟩
  have hlocal := profile_ratio_one_on_small_interval
    m f F k₀ f₂ F₂ a c L C ha hc hL hC hCL hsmall
    (fun r hr => hFpos r (hsubHalfOpen r hr))
    hFlower hFupper (hkcont.mono hsubClosed)
    (fun r hr => hkevent r (hsubHalfOpen r hr))
    hkzero hkbounded (hfluxcont.mono hsubClosed)
    hfDiff hFDiff
    (fun r hr => hdf r (hsubOpen r hr))
    (fun r hr => hdF r (hsubOpen r hr))
    (fun r hr => hode_f r (hsubOpen r hr))
    (fun r hr => hode_F r (hsubOpen r hr))
  exact ⟨a, ha, haR, hlocal⟩

end

end BrezisOP6
