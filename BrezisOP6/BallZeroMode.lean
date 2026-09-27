import BrezisOP6.ProfileContactFromODE
import BrezisOP6.ZeroModeEndpoint

/-!
# Finite-ball contact positivity closes the zero-mode Picone estimate

This is the last one-dimensional implication in the new argument.  The
contact domain and a small-radius start give a strictly positive residual
on the finite ball, and the interval Picone identity then gives a
nonnegative quadratic form.  Endpoint regularity and integrability for the
test coefficient remain explicit analytic inputs.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- A finite-ball profile pair satisfying the contact-domain inequalities
has a nonnegative zero-mode quadratic form for every admissible radial
coefficient.  All profile ODE hypotheses are restricted to `(0,R]`. -/
theorem ball_zero_mode_nonnegative_of_contact_domain
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hMpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (haux : ∀ r ∈ Set.Ioc 0 R, ∃ X : ℝ,
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
    (hb : ∀ r ∈ Set.Ioc 0 R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R)
    (hsq_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        MeasureTheory.volume δ R)
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        MeasureTheory.volume δ R)
    (hrem_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
        MeasureTheory.volume δ R)
    (hfactor : Filter.Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hbcont : ContinuousAt b 0) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r := by
  have hpositive := profileContact_positive_on_ball_interval
    m f F f₂ F₂ R hFpos hMpos hfDiff hFDiff
      hdf hdF hode_f hode_F haux hnear
  apply profilePicone_zero_mode_nonnegative m f F b db f₂ F₂ R hR
    hFpos hMpos hfDiff hFDiff hdf hdF hode_f hode_F hb
  · intro r hr
    have h := hpositive r hr
    simpa only [profileContactResidual, profileM, ratioM] using h.le
  · exact hbR
  · exact hDint
  · exact hsq_int
  · exact hflux_int
  · exact hrem_int
  · exact hfactor
  · exact hbcont

end

end BrezisOP6
