import BrezisOP6.ProfileContactFromODE

/-!
# Contact residual at the finite-ball edge

The first-contact argument runs on every compact subinterval strictly
inside the ball.  Continuity of the residual then gives a nonnegative value
at the outer endpoint.  This is exactly the endpoint sign needed for the
Picone integral and does not invoke the finite-ball ODE at the boundary.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

/-- Strict contact positivity at every interior radius.  The one-sided
endpoint passage used by the companion nonnegativity theorem is not
needed here.  Exposing this interior conclusion supplies a quantitative
lower bound on every compact annulus. -/
theorem profileContact_positive_on_open_ball_of_interior_ode
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ) (R : ℝ)
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
        0 < profileContactResidual f F r) :
    ∀ r ∈ Ioo (0 : ℝ) R,
      0 < profileContactResidual f F r := by
  intro r hr
  have hsubClosed (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
      x ∈ Ioc (0 : ℝ) R :=
    ⟨hx.1, hx.2.trans hr.2.le⟩
  have hsubOpen (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
      x ∈ Ioo (0 : ℝ) R :=
    ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩
  have hnear' : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x, 0 < x → x < ρ → x ≤ r →
        0 < profileContactResidual f F x := by
    obtain ⟨ρ, hρ, hstart⟩ := hnear
    exact ⟨ρ, hρ, fun x hx hxρ hxr =>
      hstart x hx hxρ (hxr.trans hr.2.le)⟩
  exact profileContact_positive_on_ball_interval
    m f F f₂ F₂ r
    (fun x hx => hFpos x (hsubClosed x hx))
    (fun x hx => hMpos x (hsubClosed x hx))
    hfDiff hFDiff
    (fun x hx => hdf x (hsubOpen x hx))
    (fun x hx => hdF x (hsubOpen x hx))
    (fun x hx => hode_f x (hsubOpen x hx))
    (fun x hx => hode_F x (hsubOpen x hx))
    (fun x hx => haux x (hsubOpen x hx))
    hnear' r ⟨hr.1, le_rfl⟩

theorem profileContact_nonnegative_on_ball_of_interior_ode
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
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
      (𝓝[<] R) (𝓝 (profileContactResidual f F R))) :
    ∀ r ∈ Ioc (0 : ℝ) R,
      0 ≤ profileContactResidual f F r := by
  have hposInterior : ∀ r ∈ Ioo (0 : ℝ) R,
      0 < profileContactResidual f F r := by
    intro r hr
    have hsubClosed (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
        x ∈ Ioc (0 : ℝ) R :=
      ⟨hx.1, hx.2.trans hr.2.le⟩
    have hsubOpen (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
        x ∈ Ioo (0 : ℝ) R :=
      ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩
    have hnear' : ∃ ρ : ℝ, 0 < ρ ∧
        ∀ x, 0 < x → x < ρ → x ≤ r →
          0 < profileContactResidual f F x := by
      obtain ⟨ρ, hρ, hstart⟩ := hnear
      exact ⟨ρ, hρ, fun x hx hxρ hxr =>
        hstart x hx hxρ (hxr.trans hr.2.le)⟩
    exact profileContact_positive_on_ball_interval
      m f F f₂ F₂ r
      (fun x hx => hFpos x (hsubClosed x hx))
      (fun x hx => hMpos x (hsubClosed x hx))
      hfDiff hFDiff
      (fun x hx => hdf x (hsubOpen x hx))
      (fun x hx => hdF x (hsubOpen x hx))
      (fun x hx => hode_f x (hsubOpen x hx))
      (fun x hx => hode_F x (hsubOpen x hx))
      (fun x hx => haux x (hsubOpen x hx))
      hnear' r ⟨hr.1, le_rfl⟩
  have hlim : Tendsto (profileContactResidual f F)
      (𝓝[<] R) (𝓝 (profileContactResidual f F R)) := hSRcont
  have hposEvent : ∀ᶠ r in 𝓝[<] R,
      0 ≤ profileContactResidual f F r := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hR).filter_mono nhdsWithin_le_nhds]
      with r hrR hr0
    exact (hposInterior r ⟨hr0, hrR⟩).le
  have hRnonneg : 0 ≤ profileContactResidual f F R :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hposEvent
  intro r hr
  rcases lt_or_eq_of_le hr.2 with hrR | heq
  · exact (hposInterior r ⟨hr.1, hrR⟩).le
  · simpa [heq] using hRnonneg

end

end BrezisOP6
