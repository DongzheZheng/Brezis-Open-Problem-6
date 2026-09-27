import BrezisOP6.OriginRatioGerm

/-!
# From the verified origin germ to ordinary positive-radius ODE uniqueness

The origin contraction establishes equality of the two profiles on an
actual interval.  Thus they have equal value and first derivative at a
strictly positive radius.  The only uniqueness input below is the usual
nonsingular initial-value theorem there.  In particular, no uniqueness
statement at the regular-singular origin is assumed.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

theorem ratio_origin_one_implies_identically_one_of_regular_ode_uniqueness
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (R α AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) R))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) R,
      k₀ =ᶠ[𝓝 r] profileK f F)
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
        r (F r) (deriv F r) (F₂ r))
    (hPositiveIVPUnique :
      ∀ s ∈ Ioo (0 : ℝ) R,
        f s = F s → deriv f s = deriv F s →
        ∀ r ∈ Ioc (0 : ℝ) R, f r = F r) :
    k₀ 0 = 1 → ∀ r ∈ Ioc (0 : ℝ) R, k₀ r = 1 := by
  intro hkzero r hr
  obtain ⟨a, ha, haR, hlocal⟩ :=
    profile_ratio_one_on_some_origin_interval
      m f F k₀ f₂ F₂ R α AF BF hR hα hFTaylor hFpos
      hkcont hkevent hkzero hfluxcont hfDiff hFDiff
      hdf hdF hode_f hode_F
  let s : ℝ := a / 2
  have hs : s ∈ Ioo (0 : ℝ) a := by
    dsimp [s]
    constructor <;> linarith
  have hsR : s ∈ Ioo (0 : ℝ) R :=
    ⟨hs.1, lt_trans hs.2 haR⟩
  have hprofileEq : ∀ t ∈ Ioo (0 : ℝ) a, f t = F t := by
    intro t ht
    have htR : t ∈ Ioc (0 : ℝ) R :=
      ⟨ht.1, (le_of_lt (lt_trans ht.2 haR))⟩
    have hkt : k₀ t = 1 := hlocal t ⟨ht.1.le, ht.2.le⟩
    have hquot : f t / F t = 1 := by
      calc
        f t / F t = profileK f F t := rfl
        _ = k₀ t := (hkevent t htR).eq_of_nhds.symm
        _ = 1 := hkt
    have hval := (div_eq_iff (ne_of_gt (hFpos t htR))).mp hquot
    simpa using hval
  have hnear : f =ᶠ[𝓝 s] F := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact hprofileEq t ht
  have hvalue : f s = F s := hprofileEq s hs
  have hderiv : deriv f s = deriv F s := hnear.deriv_eq
  have hsame : f r = F r :=
    hPositiveIVPUnique s hsR hvalue hderiv r hr
  have hkr : k₀ r = profileK f F r :=
    (hkevent r hr).eq_of_nhds
  rw [hkr, profileK, hsame]
  exact div_self (ne_of_gt (hFpos r hr))

end

end BrezisOP6
