import BrezisOP6.EtaGlobal

/-!
# The normalized-growth barrier on an open finite ball

The comparison proof is applied on each smaller closed ball.  Hence the
second-order profile equation is used only at radii strictly below the
original outer boundary.
-/

namespace BrezisOP6

open Set

noncomputable section

theorem profile_eta_barrier_on_open_interval
    (d : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (hηcont : ContinuousOn (profileEta f F) (Icc (0 : ℝ) R))
    (hnear : ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ →
        profileEta f F r < r / Real.sqrt 2)
    (hFpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < F r)
    (hFlt : ∀ r ∈ Ioo (0 : ℝ) R, F r < 1)
    (hkpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < profileK f F r)
    (hMpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < profileM f F r)
    (hylt : ∀ r ∈ Ioo (0 : ℝ) R, profileY F r < 1)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hprofiles : ∀ r ∈ Ioo (0 : ℝ) R,
      ∃ f₁ F₁ f₂ F₂ : ℝ,
        HasDerivAt f f₁ r ∧ HasDerivAt F F₁ r ∧
        HasDerivAt (deriv f) f₂ r ∧
        HasDerivAt (deriv F) F₂ r ∧
        radialODEAt ((d : ℝ) + 3) r (f r) f₁ f₂ ∧
        radialODEAt ((d : ℝ) + 3) r (F r) F₁ F₂) :
    ∀ r ∈ Ioo (0 : ℝ) R,
      profileEta f F r < r / Real.sqrt 2 := by
  intro r hr
  have hsub (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
      x ∈ Ioo (0 : ℝ) R :=
    ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩
  have hcont : ContinuousOn (profileEta f F) (Icc (0 : ℝ) r) :=
    hηcont.mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans hr.2.le⟩)
  exact profile_eta_barrier_on_positive_interval d f F r hr.1
    hcont hnear
    (fun x hx => hFpos x (hsub x hx))
    (fun x hx => hFlt x (hsub x hx))
    (fun x hx => hkpos x (hsub x hx))
    (fun x hx => hMpos x (hsub x hx))
    (fun x hx => hylt x (hsub x hx))
    hfDiff hFDiff
    (fun x hx => hprofiles x (hsub x hx))
    r ⟨hr.1, le_rfl⟩

end

end BrezisOP6
