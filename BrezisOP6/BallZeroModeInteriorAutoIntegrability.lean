import BrezisOP6.BallZeroModeInterior
import BrezisOP6.ProfilePiconeRemainderMeasurable

/-!
# Automatic annular integrability in the zero-mode contact theorem

The two nonnegative Picone pieces are integrable because their sum is the
integrable density minus the integrable flux derivative. The remainder is
measurable from the profile functions and the continuous punctured mode.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem ball_zero_mode_nonnegative_of_contact_domain_auto_integrability_interior
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hMpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < profileM f F r)
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
    (haux : ∀ r ∈ Ioo (0 : ℝ) R, ∃ X : ℝ,
      0 < profileY F r ∧ profileY F r < 1 ∧
      0 < profileK f F r ∧ 0 < profileEta f F r ∧
      profileEta f F r ^ 2 < r ^ 2 / 2 ∧
      0 < X ∧ X < 1 ∧
      profileM f F r * profileEta f F r =
        profileK f F r * X * profileY F r ∧
      profileY F r ≤ F r ^ 2)
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r)
    (hSRcont : Tendsto (profileContactResidual f F)
      (𝓝[<] R) (𝓝 (profileContactResidual f F R)))
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R)
    (hflux_cont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F b)
        (uIcc δ R))
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        MeasureTheory.volume δ R)
    (hfactor : Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r := by
  have hS := profileContact_nonnegative_on_ball_of_interior_ode
    m f F f₂ F₂ R hR hFpos hMpos hfDiff hFDiff
    hdf hdF hode_f hode_F haux hnear hSRcont
  have hbCont : ContinuousOn b (Ioo (0 : ℝ) R) := by
    intro r hr
    exact (hb r hr).continuousAt.continuousWithinAt
  have hParts (δ : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
      IntervalIntegrable (profilePiconeSquare m f F b db)
        volume δ R ∧
      IntervalIntegrable (profilePiconeRemainder m f F b)
        volume δ R := by
    have hDintAnn : IntervalIntegrable
        (profilePiconeDensity m f F b db) volume δ R := by
      apply hDint.mono_set
      rw [uIcc_of_le hδR, uIcc_of_le hR.le]
      intro r hr
      exact ⟨le_trans hδ.le hr.1, hr.2⟩
    have hbContAnn : ContinuousOn b (Ioo δ R) := by
      apply hbCont.mono
      intro r hr
      exact ⟨hδ.trans hr.1, hr.2⟩
    have hremMeas :=
      profilePiconeRemainder_aestronglyMeasurable_of_b_continuousOn
        m f F b δ R hfDiff.continuous.measurable
          hFDiff.continuous.measurable hbContAnn
    apply profilePicone_annulus_parts_intervalIntegrable
      m f F b db f₂ F₂ δ R hδ hδR
      (fun r hr => hFpos r (by
        rw [uIcc_of_le hδR] at hr
        exact ⟨lt_of_lt_of_le hδ hr.1, hr.2⟩))
      (fun r hr => hMpos r (by
        rw [uIcc_of_le hδR] at hr
        exact ⟨lt_of_lt_of_le hδ hr.1, hr.2⟩))
      hfDiff hFDiff
      (fun r hr => hdf r (by
        rw [uIoo_of_le hδR] at hr
        exact ⟨hδ.trans hr.1, hr.2⟩))
      (fun r hr => hdF r (by
        rw [uIoo_of_le hδR] at hr
        exact ⟨hδ.trans hr.1, hr.2⟩))
      (fun r hr => hode_f r (by
        rw [uIoo_of_le hδR] at hr
        exact ⟨hδ.trans hr.1, hr.2⟩))
      (fun r hr => hode_F r (by
        rw [uIoo_of_le hδR] at hr
        exact ⟨hδ.trans hr.1, hr.2⟩))
      (fun r hr => hb r (by
        rw [uIoo_of_le hδR] at hr
        exact ⟨hδ.trans hr.1, hr.2⟩))
      (fun r hr => by
        have hr' : r ∈ Ioc (0 : ℝ) R := by
          rw [uIcc_of_le hδR] at hr
          exact ⟨lt_of_lt_of_le hδ hr.1, hr.2⟩
        simpa only [profileContactResidual, profileM, ratioM] using
          hS r hr')
      hDintAnn (hflux_int δ hδ hδR) hremMeas
  exact ball_zero_mode_nonnegative_of_contact_domain_interior
    m f F b db f₂ F₂ R hR hFpos hMpos hfDiff hFDiff
    hdf hdF hode_f hode_F haux hnear hSRcont
    hb hbR hDint
    (fun δ hδ hδR => (hParts δ hδ hδR).1)
    hflux_cont hflux_int
    (fun δ hδ hδR => (hParts δ hδ hδR).2)
    hfactor hblim

end

end BrezisOP6
