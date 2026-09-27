import BrezisOP6.LogRadius
import BrezisOP6.FlowFromProfiles
import BrezisOP6.EtaFlowFromProfiles
import BrezisOP6.ContactGlobal

/-!
# Contact positivity along the actual radial profile pair

The five-dimensional trajectory used by the contact theorem is obtained by
setting `r=exp s` in the two original profile equations.  Auxiliary bounds
and the small-radius sign of `S` remain explicit analytic hypotheses.
-/

namespace BrezisOP6

noncomputable section

def profileLogRadius (s : ℝ) : ℝ := Real.exp s
def profileLogT (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  profileT F (Real.exp s)
def profileLogY (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  profileY F (Real.exp s)
def profileLogK (f F : ℝ → ℝ) (s : ℝ) : ℝ :=
  profileK f F (Real.exp s)
def profileLogEta (f F : ℝ → ℝ) (s : ℝ) : ℝ :=
  profileEta f F (Real.exp s)

/-- The radial Picone residual expressed directly through the two profiles. -/
def profileContactResidual (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  contactResidual r (profileT F r) (profileY F r)
    (profileM f F r) (profileEta f F r)

theorem profileContactResidual_log_eq
    (f F : ℝ → ℝ) (s : ℝ) :
    residualAlong profileLogRadius (profileLogT F) (profileLogY F)
      (profileLogK f F) (profileLogEta f F) s =
      profileContactResidual f F (Real.exp s) := by
  rfl

/-- All five logarithmic-radius equations follow from the two original
radial ODEs.  Neither the `y`, `k`, nor the `η` flow is an independent input. -/
theorem profileLog_five_flows_from_ODE
    (m : ℕ) (f F : ℝ → ℝ) (s f₁ F₁ f₂ F₂ : ℝ)
    (hFpos : 0 < F (Real.exp s))
    (hMpos : 0 < profileM f F (Real.exp s))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ (Real.exp s))
    (hF : HasDerivAt F F₁ (Real.exp s))
    (hdf : HasDerivAt (deriv f) f₂ (Real.exp s))
    (hdF : HasDerivAt (deriv F) F₂ (Real.exp s))
    (hode_f : radialODEAt ((m : ℝ) + 3)
      (Real.exp s) (f (Real.exp s)) f₁ f₂)
    (hode_F : radialODEAt ((m : ℝ) + 3)
      (Real.exp s) (F (Real.exp s)) F₁ F₂) :
    HasDerivAt profileLogRadius (profileLogRadius s) s ∧
    HasDerivAt (profileLogT F)
      (profileLogT F s * (2 - profileLogY F s)) s ∧
    HasDerivAt (profileLogY F)
      (profileLogY F s ^ 2 - ((m : ℝ) + 3) * profileLogY F s +
        profileLogRadius s ^ 2 - profileLogT F s ^ 2) s ∧
    HasDerivAt (profileLogK f F)
      ((profileLogK f F s ^ 2 - 1) * profileLogEta f F s) s ∧
    HasDerivAt (profileLogEta f F)
      (profileLogK f F s * profileLogT F s ^ 2 -
        (((m : ℝ) + 3) - 2 * profileLogY F s) *
          profileLogEta f F s -
        2 * profileLogK f F s * profileLogEta f F s ^ 2) s := by
  let r : ℝ := Real.exp s
  have hr : 0 < r := Real.exp_pos s
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hMne : profileM f F r ≠ 0 := ne_of_gt hMpos
  have hTdiff : DifferentiableAt ℝ (profileT F) r := by
    exact ((hasDerivAt_id r).mul hF).differentiableAt
  have hyDiff : DifferentiableAt ℝ (profileY F) r := by
    unfold profileY
    exact (((hasDerivAt_id r).mul hdF).div hF hFne).const_sub 1
      |>.differentiableAt
  have hk := profileK_hasDerivAt f F r f₁ F₁ hf hF hFne
  have hkDiff : DifferentiableAt ℝ (profileK f F) r :=
    hk.differentiableAt
  have hetaDiff := profileEta_differentiableAt_from_profiles m f F r
    f₁ F₁ f₂ F₂ hr hFpos hMpos hfDiff hFDiff hf hF hdf hdF
  have htFlow := profileT_flow F r F₁ hFpos hF
  have hyFlow := profileY_flow ((m : ℝ) + 3) F r F₁ F₂
    hFpos hF hdF hode_F
  have hkFlow :
      r * deriv (profileK f F) r =
        (profileK f F r ^ 2 - 1) * profileEta f F r := by
    change r * deriv (profileK f F) r =
      profileM f F r *
        (r * deriv (profileK f F) r / profileM f F r)
    field_simp [hMne]
  have hetaFlow := profileEta_flow_from_ODE m f F r f₁ F₁ f₂ F₂
    hr hFpos hMpos hfDiff hFDiff hf hF hdf hdF hode_f hode_F
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [profileLogRadius] using Real.hasDerivAt_exp s
  · simpa [profileLogT, profileLogY] using
      (hasDerivAt_exp_comp_of_radial_flow hTdiff htFlow)
  · simpa [profileLogY, profileLogRadius, profileLogT] using
      (hasDerivAt_exp_comp_of_radial_flow hyDiff hyFlow)
  · simpa [profileLogK, profileLogEta] using
      (hasDerivAt_exp_comp_of_radial_flow hkDiff hkFlow)
  · simpa [profileLogEta, profileLogK, profileLogT, profileLogY] using
      (hasDerivAt_exp_comp_of_radial_flow hetaDiff hetaFlow)

/-- Contact positivity on a finite logarithmic-radius interval.  The
auxiliary inequalities are assumed for the actual `f,F` trajectory, while
the derivative-at-contact condition is supplied by `ContactGlobal`. -/
theorem profileContact_positive_on_log_interval
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ) (a b : ℝ)
    (hSa : 0 < profileContactResidual f F (Real.exp a))
    (hFpos : ∀ r ∈ Set.Icc (Real.exp a) (Real.exp b), 0 < F r)
    (hMpos : ∀ r ∈ Set.Icc (Real.exp a) (Real.exp b),
      0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Icc (Real.exp a) (Real.exp b),
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Icc (Real.exp a) (Real.exp b),
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Icc (Real.exp a) (Real.exp b),
      radialODEAt ((m : ℝ) + 3)
      r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Icc (Real.exp a) (Real.exp b),
      radialODEAt ((m : ℝ) + 3)
      r (F r) (deriv F r) (F₂ r))
    (haux : ∀ r ∈ Set.Icc (Real.exp a) (Real.exp b), ∃ X : ℝ,
      0 < profileY F r ∧ profileY F r < 1 ∧
      0 < profileK f F r ∧ 0 < profileEta f F r ∧
      profileEta f F r ^ 2 < r ^ 2 / 2 ∧
      0 < X ∧ X < 1 ∧
      profileM f F r * profileEta f F r =
        profileK f F r * X * profileY F r ∧
      profileY F r ≤ F r ^ 2) :
    ∀ s ∈ Set.Icc a b,
      0 < profileContactResidual f F (Real.exp s) := by
  have hradial (s : ℝ) (hs : s ∈ Set.Icc a b) :
      Real.exp s ∈ Set.Icc (Real.exp a) (Real.exp b) :=
    ⟨Real.exp_le_exp.mpr hs.1, Real.exp_le_exp.mpr hs.2⟩
  have hflows (s : ℝ) (hs : s ∈ Set.Icc a b) :=
    profileLog_five_flows_from_ODE m f F s
      (deriv f (Real.exp s)) (deriv F (Real.exp s))
      (f₂ (Real.exp s)) (F₂ (Real.exp s))
      (hFpos (Real.exp s) (hradial s hs))
      (hMpos (Real.exp s) (hradial s hs))
      hfDiff hFDiff
      (hfDiff (Real.exp s)).hasDerivAt
      (hFDiff (Real.exp s)).hasDerivAt
      (hdf (Real.exp s) (hradial s hs))
      (hdF (Real.exp s) (hradial s hs))
      (hode_f (Real.exp s) (hradial s hs))
      (hode_F (Real.exp s) (hradial s hs))
  have hcont : ContinuousOn (residualAlong profileLogRadius
      (profileLogT F) (profileLogY F)
      (profileLogK f F) (profileLogEta f F)) (Set.Icc a b) := by
    intro s hs
    obtain ⟨hr, ht, hy, hk, heta⟩ := hflows s hs
    exact ((residualAlong_hasDerivAt_of_flow hr ht hy hk heta).continuousAt).continuousWithinAt
  have hSaLog : 0 < residualAlong profileLogRadius
      (profileLogT F) (profileLogY F)
      (profileLogK f F) (profileLogEta f F) a := by
    simpa only [profileContactResidual_log_eq] using hSa
  have hn : 2 < (m : ℝ) + 3 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpositive := residualAlong_positive_on_interval
    (r := profileLogRadius) (t := profileLogT F)
    (y := profileLogY F) (k := profileLogK f F)
    (eta := profileLogEta f F)
    (a := a) (b := b) (n := (m : ℝ) + 3)
    hcont hSaLog hn
    (by intro s has hsb; exact (hflows s ⟨has.le, hsb⟩).1)
    (by intro s has hsb; exact (hflows s ⟨has.le, hsb⟩).2.1)
    (by intro s has hsb; exact (hflows s ⟨has.le, hsb⟩).2.2.1)
    (by intro s has hsb; exact (hflows s ⟨has.le, hsb⟩).2.2.2.1)
    (by intro s has hsb; exact (hflows s ⟨has.le, hsb⟩).2.2.2.2)
    (by
      intro s has hsb
      let r : ℝ := Real.exp s
      have hr : r ∈ Set.Icc (Real.exp a) (Real.exp b) :=
        hradial s ⟨has.le, hsb⟩
      obtain ⟨X, hy0, hy1, hk0, heta0, hetaSmall,
        hX0, hX1, hchi, hq⟩ := haux r hr
      refine ⟨X, F r ^ 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [profileLogK, profileM, ratioM] using hMpos r hr
      · simpa [profileLogY] using hy0
      · simpa [profileLogY] using hy1
      · simpa [profileLogK] using hk0
      · simpa [profileLogEta] using heta0
      · simpa [profileLogEta, profileLogRadius] using hetaSmall
      · exact hX0
      · exact hX1
      · simpa [profileLogK, profileLogY, profileLogEta,
          profileM, ratioM] using hchi
      · simpa [profileLogY] using hq
      · simp only [profileLogT, profileLogRadius, profileT]
        ring)
  intro s hs
  rw [← profileContactResidual_log_eq]
  exact hpositive s hs

/-- The ball-profile version: all ODE, denominator, and auxiliary bounds
are required only on `(0,R]`.  A one-sided sign near zero starts the
first-contact argument.  The conclusion applies to every inner regular
interval `[δ,R]` by restriction. -/
theorem profileContact_positive_on_ball_interval
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ) (R : ℝ)
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
        0 < profileContactResidual f F r) :
    ∀ r ∈ Set.Ioc 0 R, 0 < profileContactResidual f F r := by
  intro r hr
  obtain ⟨ρ, hρ, hsmall⟩ := hnear
  let δ : ℝ := min (ρ / 2) (r / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · linarith
    · linarith [hr.1]
  have hδρ : δ < ρ := by
    have hle := min_le_left (ρ / 2) (r / 2)
    dsimp [δ]
    linarith
  have hδr : δ < r := by
    have hle := min_le_right (ρ / 2) (r / 2)
    dsimp [δ]
    linarith [hr.1]
  have hSδ : 0 < profileContactResidual f F δ :=
    hsmall δ hδpos hδρ (le_trans hδr.le hr.2)
  have hSa : 0 < profileContactResidual f F
      (Real.exp (Real.log δ)) := by
    simpa only [Real.exp_log hδpos] using hSδ
  have hwithin (x : ℝ)
      (hx : x ∈ Set.Icc (Real.exp (Real.log δ))
        (Real.exp (Real.log r))) : x ∈ Set.Ioc 0 R := by
    have hleft : δ ≤ x := by
      simpa only [Real.exp_log hδpos] using hx.1
    have hright : x ≤ r := by
      simpa only [Real.exp_log hr.1] using hx.2
    exact ⟨lt_of_lt_of_le hδpos hleft, hright.trans hr.2⟩
  have hinterval := profileContact_positive_on_log_interval
    m f F f₂ F₂ (Real.log δ) (Real.log r) hSa
    (by intro x hx; exact hFpos x (hwithin x hx))
    (by intro x hx; exact hMpos x (hwithin x hx))
    hfDiff hFDiff
    (by intro x hx; exact hdf x (hwithin x hx))
    (by intro x hx; exact hdF x (hwithin x hx))
    (by intro x hx; exact hode_f x (hwithin x hx))
    (by intro x hx; exact hode_F x (hwithin x hx))
    (by intro x hx; exact haux x (hwithin x hx))
  have hlog : Real.log δ ≤ Real.log r :=
    (Real.log_lt_log hδpos hδr).le
  have hSr := hinterval (Real.log r) ⟨hlog, le_rfl⟩
  simpa only [Real.exp_log hr.1] using hSr

/-- A one-sided small-radius sign and the global auxiliary inequalities
propagate `S>0` to every positive radius.  Nothing is evaluated at `r=0`:
in particular, this theorem does not assert continuity of the quotient
variables at the origin. -/
theorem profileContact_positive_on_positive_axis
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ)
    (hFpos : ∀ r, 0 < r → 0 < F r)
    (hMpos : ∀ r, 0 < r → 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r, 0 < r → HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r, 0 < r → HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r, 0 < r → radialODEAt ((m : ℝ) + 3)
      r (F r) (deriv F r) (F₂ r))
    (haux : ∀ r, 0 < r → ∃ X : ℝ,
      0 < profileY F r ∧ profileY F r < 1 ∧
      0 < profileK f F r ∧ 0 < profileEta f F r ∧
      profileEta f F r ^ 2 < r ^ 2 / 2 ∧
      0 < X ∧ X < 1 ∧
      profileM f F r * profileEta f F r =
        profileK f F r * X * profileY F r ∧
      profileY F r ≤ F r ^ 2)
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → 0 < profileContactResidual f F r) :
    ∀ R, 0 < R → 0 < profileContactResidual f F R := by
  intro R hR
  obtain ⟨ρ, hρ, hsmall⟩ := hnear
  let δ : ℝ := min (ρ / 2) (R / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · linarith
    · linarith
  have hδρ : δ < ρ := by
    have hle := min_le_left (ρ / 2) (R / 2)
    dsimp [δ]
    linarith
  have hδR : δ < R := by
    have hle := min_le_right (ρ / 2) (R / 2)
    dsimp [δ]
    linarith
  have hSδ : 0 < profileContactResidual f F δ :=
    hsmall δ hδpos hδρ
  have hSa : 0 < profileContactResidual f F
      (Real.exp (Real.log δ)) := by
    simpa only [Real.exp_log hδpos] using hSδ
  have hlog : Real.log δ ≤ Real.log R :=
    (Real.log_lt_log hδpos hδR).le
  have hinterval := profileContact_positive_on_log_interval
    m f F f₂ F₂ (Real.log δ) (Real.log R)
    hSa
    (by intro r hr; exact hFpos r (lt_of_lt_of_le
      (Real.exp_pos (Real.log δ)) hr.1))
    (by intro r hr; exact hMpos r (lt_of_lt_of_le
      (Real.exp_pos (Real.log δ)) hr.1))
    hfDiff hFDiff
    (by intro r hr; exact hdf r (lt_of_lt_of_le
      (Real.exp_pos (Real.log δ)) hr.1))
    (by intro r hr; exact hdF r (lt_of_lt_of_le
      (Real.exp_pos (Real.log δ)) hr.1))
    (by intro r hr; exact hode_f r (lt_of_lt_of_le
      (Real.exp_pos (Real.log δ)) hr.1))
    (by intro r hr; exact hode_F r (lt_of_lt_of_le
      (Real.exp_pos (Real.log δ)) hr.1))
    (by intro r hr; exact haux r (lt_of_lt_of_le
      (Real.exp_pos (Real.log δ)) hr.1))
  have hSR := hinterval (Real.log R) ⟨hlog, le_rfl⟩
  simpa only [Real.exp_log hR] using hSR

/-- The positive-axis conclusion applies, in particular, to every compact
regular interval `[δ,R]`. -/
theorem profileContact_positive_on_finite_interval
    (f F : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ)
    (hpositive : ∀ r, 0 < r → 0 < profileContactResidual f F r) :
    ∀ r ∈ Set.Icc δ R, 0 < profileContactResidual f F r := by
  intro r hr
  exact hpositive r (lt_of_lt_of_le hδ hr.1)

/-- The same conclusion holds on every punctured interval `(0,R]`; the
small-radius endpoint remains one-sided. -/
theorem profileContact_positive_on_punctured_interval
    (f F : ℝ → ℝ) (R : ℝ)
    (hpositive : ∀ r, 0 < r → 0 < profileContactResidual f F r) :
    ∀ r ∈ Set.Ioc (0 : ℝ) R, 0 < profileContactResidual f F r := by
  intro r hr
  exact hpositive r hr.1

end

end BrezisOP6
