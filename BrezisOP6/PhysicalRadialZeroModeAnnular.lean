import BrezisOP6.PhysicalRadialContactData
import BrezisOP6.ZeroModeAnnularCoercivitySharp

/-!
# Annular zero-mode coercivity from public radial profile data

For any admissible scalar radial mean, the profile record alone supplies
the strict contact coefficient and vanishing origin flux factor.  The
square and remainder of the Picone decomposition are automatically
integrable on each positive annulus from the integrable original density
and the regular boundary flux.  Thus they are not additional hypotheses.
-/

namespace BrezisOP6

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem PhysicalRadialData.zero_mode_annular_l2
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (b db : ℝ → ℝ) (δ ρ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable
      (profilePiconeDensity m p.f p.F b db) volume 0 R)
    (hBsqInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hflux_cont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m p.f p.F b)
        (uIcc ε R))
    (hflux_int : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m p.f p.F b))
        volume ε R)
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    ∃ lam : ℝ, 0 < lam ∧
      lam * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          profilePiconeDensity m p.f p.F b db r := by
  obtain ⟨hMpos, hSnonneg, hSpos, hfactor⟩ :=
    PhysicalRadialData.contact_coercivity_certificate m R p
  have hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 p.F := p.hFC2.of_le (by norm_num)
  have hfDiff : Differentiable ℝ p.f :=
    fun r => hfC1.differentiable_one r
  have hFDiff : Differentiable ℝ p.F :=
    fun r => hFC1.differentiable_one r
  let f₂ : ℝ → ℝ := deriv (deriv p.f)
  let F₂ : ℝ → ℝ := deriv (deriv p.F)
  have hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv p.f) (f₂ r) r := by
    intro r _
    exact radial_profile_deriv_hasDerivAt p.f p.hfC2 r
  have hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv p.F) (F₂ r) r := by
    intro r _
    exact radial_profile_deriv_hasDerivAt p.F p.hFC2 r
  have hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (p.f r) (deriv p.f r) (f₂ r) := by
    intro r hr
    exact p.hfODE r hr.1 hr.2
  have hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (p.F r) (deriv p.F r) (F₂ r) := by
    intro r hr
    exact p.hFodeAll r hr.1
  have hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < p.F r := by
    intro r hr
    exact p.hFposAll r hr.1
  have hbCont : ContinuousOn b (Ioo (0 : ℝ) R) := by
    intro r hr
    exact (hb r hr).continuousAt.continuousWithinAt
  have hParts (ε : ℝ) (hε : 0 < ε) (hεR : ε ≤ R) :
      IntervalIntegrable (profilePiconeSquare m p.f p.F b db)
        volume ε R ∧
      IntervalIntegrable (profilePiconeRemainder m p.f p.F b)
        volume ε R := by
    have hDintAnn : IntervalIntegrable
        (profilePiconeDensity m p.f p.F b db) volume ε R := by
      apply hDint.mono_set
      rw [uIcc_of_le hεR, uIcc_of_le p.hR.le]
      intro r hr
      exact ⟨le_trans hε.le hr.1, hr.2⟩
    have hbContAnn : ContinuousOn b (Ioo ε R) := by
      apply hbCont.mono
      intro r hr
      exact ⟨hε.trans hr.1, hr.2⟩
    have hremMeas :=
      profilePiconeRemainder_aestronglyMeasurable_of_b_continuousOn
        m p.f p.F b ε R hfDiff.continuous.measurable
          hFDiff.continuous.measurable hbContAnn
    apply profilePicone_annulus_parts_intervalIntegrable
      m p.f p.F b db f₂ F₂ ε R hε hεR
      (fun r hr => hFpos r (by
        rw [uIcc_of_le hεR] at hr
        exact ⟨lt_of_lt_of_le hε hr.1, hr.2⟩))
      (fun r hr => hMpos r (by
        rw [uIcc_of_le hεR] at hr
        exact ⟨lt_of_lt_of_le hε hr.1, hr.2⟩))
      hfDiff hFDiff
      (fun r hr => hdf r (by
        rw [uIoo_of_le hεR] at hr
        exact ⟨hε.trans hr.1, hr.2⟩))
      (fun r hr => hdF r (by
        rw [uIoo_of_le hεR] at hr
        exact ⟨hε.trans hr.1, hr.2⟩))
      (fun r hr => hode_f r (by
        rw [uIoo_of_le hεR] at hr
        exact ⟨hε.trans hr.1, hr.2⟩))
      (fun r hr => hode_F r (by
        rw [uIoo_of_le hεR] at hr
        exact ⟨hε.trans hr.1, hr.2⟩))
      (fun r hr => hb r (by
        rw [uIoo_of_le hεR] at hr
        exact ⟨hε.trans hr.1, hr.2⟩))
      (fun r hr => by
        have hr' : r ∈ Ioc (0 : ℝ) R := by
          rw [uIcc_of_le hεR] at hr
          exact ⟨lt_of_lt_of_le hε hr.1, hr.2⟩
        simpa only [profileContactResidual, profileM, ratioM] using
          hSnonneg r hr')
      hDintAnn (hflux_int ε hε hεR) hremMeas
  exact profilePicone_zero_mode_annular_l2_from_profiles_sharp
    m p.f p.F b db f₂ F₂ δ ρ R
    hδ hδρ hρR hfC1 hFC1 hFpos hMpos
    hfDiff hFDiff hdf hdF hode_f hode_F hb
    hSnonneg hSpos hbR hDint hBsqInt
    (fun ε hε hεR => (hParts ε hε hεR).1)
    hflux_cont hflux_int
    (fun ε hε hεR => (hParts ε hε hεR).2)
    hfactor hblim

end

end BrezisOP6
