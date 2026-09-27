import BrezisOP6.ProfileContactInterior
import BrezisOP6.ZeroModeEndpointInterior

/-!
# Finite-ball zero mode with one-sided endpoint data

The contact mechanism acts on compact intervals inside the ball.  Its
nonnegative outer trace combines with the open-annulus Picone identity and
the already-proved regular-origin limit to give the full zero-mode inequality.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

theorem ball_zero_mode_nonnegative_of_contact_domain_interior
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
    (hsq_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        MeasureTheory.volume δ R)
    (hflux_cont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F b)
        (uIcc δ R))
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        MeasureTheory.volume δ R)
    (hrem_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
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
  apply profilePicone_zero_mode_nonnegative_interior
    m f F b db f₂ F₂ R hR hFpos hMpos hfDiff hFDiff
    hdf hdF hode_f hode_F hb
  · intro r hr
    have h := hS r hr
    simpa only [profileContactResidual, profileM, ratioM] using h
  · exact hbR
  · exact hDint
  · exact hsq_int
  · exact hflux_cont
  · exact hflux_int
  · exact hrem_int
  · exact hfactor
  · exact hblim

end

end BrezisOP6
