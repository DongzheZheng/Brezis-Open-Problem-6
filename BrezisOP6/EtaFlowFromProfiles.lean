import BrezisOP6.FlowFromProfiles
import BrezisOP6.Ratio
import BrezisOP6.EtaBarrier

/-!
# The normalized ratio-growth flow

Here `d : ℕ` indexes dimension `n=d+3`.  The weighted Wronskian from
`Ratio.lean` is divided by `r^(d+1) F² M`; this is exactly
`η=r k'/M`, where `k=f/F` and `M=k²-1`.  Differentiating this quotient
gives the last flow equation used by the Picone barrier argument.
-/

namespace BrezisOP6

noncomputable section
open scoped Topology

def etaFromFlux (d : ℕ) (J F M : ℝ → ℝ) (r : ℝ) : ℝ :=
  J r / (r ^ (d + 1) * F r ^ 2 * M r)

/-- An abstract weighted-flux form of the `η` equation.  It records exactly
which identities the ODE proof supplies: the Wronskian source and the `M`
flow.  All denominators are explicitly nonzero. -/
theorem etaFromFlux_flow
    (d : ℕ) (J F M : ℝ → ℝ) (r J₁ F₁ M₁ k : ℝ)
    (hr : 0 < r) (hF : 0 < F r) (hM : M r ≠ 0)
    (hJderiv : HasDerivAt J J₁ r)
    (hFderiv : HasDerivAt F F₁ r)
    (hMderiv : HasDerivAt M M₁ r)
    (hJsource : J₁ = r ^ (d + 2) * F r ^ 4 * k * M r)
    (hMflow : r * M₁ = 2 * k * M r * etaFromFlux d J F M r) :
    r * deriv (etaFromFlux d J F M) r =
      k * (r * F r) ^ 2
      - ((d : ℝ) + 3 - 2 * (1 - r * F₁ / F r)) *
          etaFromFlux d J F M r
      - 2 * k * etaFromFlux d J F M r ^ 2 := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hFne : F r ≠ 0 := ne_of_gt hF
  have hDne : r ^ (d + 1) * F r ^ 2 * M r ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hrne)
      (pow_ne_zero _ hFne)) hM
  have hpow : HasDerivAt (fun x : ℝ => x ^ (d + 1))
      (((d : ℝ) + 1) * r ^ d) r := by
    simpa using (hasDerivAt_pow (d + 1) r)
  have hden : HasDerivAt
      (fun x => x ^ (d + 1) * F x ^ 2 * M x)
      ((((d : ℝ) + 1) * r ^ d * F r ^ 2
          + r ^ (d + 1) * (2 * F r * F₁)) * M r
        + r ^ (d + 1) * F r ^ 2 * M₁) r := by
    convert ((hpow.mul (hFderiv.pow 2)).mul hMderiv) using 1
    simp only [Pi.pow_apply, Pi.mul_apply]
    ring
  have hEta : HasDerivAt (etaFromFlux d J F M)
      ((J₁ * (r ^ (d + 1) * F r ^ 2 * M r)
        - J r * ((((d : ℝ) + 1) * r ^ d * F r ^ 2
          + r ^ (d + 1) * (2 * F r * F₁)) * M r
            + r ^ (d + 1) * F r ^ 2 * M₁))
        / (r ^ (d + 1) * F r ^ 2 * M r) ^ 2) r := by
    simpa [etaFromFlux] using hJderiv.div hden hDne
  have hM₁ : M₁ =
      2 * k * M r * etaFromFlux d J F M r / r := by
    apply (eq_div_iff hrne).2
    simpa [mul_comm] using hMflow
  rw [hEta.deriv, hJsource, hM₁]
  unfold etaFromFlux
  field_simp [hrne, hFne, hM]
  ring

/-- The Wronskian quotient equals `η=r k'/M` at every point where the
denominators are nonzero. -/
theorem etaFromFlux_eq_profileEta_at
    (d : ℕ) (f F : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r) (hF : F r ≠ 0)
    (hM : profileM f F r ≠ 0)
    (hfDiff : DifferentiableAt ℝ f r)
    (hFDiff : DifferentiableAt ℝ F r) :
    etaFromFlux d (ratioFlux (d + 2) f F) F (profileM f F) r
      = profileEta f F r := by
  have hrne : r ≠ 0 := ne_of_gt hr
  unfold etaFromFlux profileEta
  rw [ratioFlux_eq_ratio (d + 2) hfDiff hFDiff hF]
  unfold profileK
  field_simp [hrne, hF, hM]
  ring

/-- A neighborhood version of the preceding identity, used to transfer
ordinary derivatives without assuming global nonvanishing of `F` or `M`. -/
theorem etaFromFlux_eventuallyEq_profileEta
    (d : ℕ) (f F : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r) (hF : F r ≠ 0)
    (hM : profileM f F r ≠ 0)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F) :
    (fun x => etaFromFlux d (ratioFlux (d + 2) f F) F
      (profileM f F) x) =ᶠ[𝓝 r] profileEta f F := by
  have hKdiff : DifferentiableAt ℝ (profileK f F) r := by
    exact (profileK_hasDerivAt f F r (deriv f r) (deriv F r)
      (hfDiff r).hasDerivAt (hFDiff r).hasDerivAt hF).differentiableAt
  have hMcont : ContinuousAt (profileM f F) r := by
    exact (((hKdiff.pow 2).sub_const 1).continuousAt :
      ContinuousAt (profileM f F) r)
  have hrEvent : ∀ᶠ x in 𝓝 r, 0 < x :=
    isOpen_Ioi.mem_nhds (show r ∈ Set.Ioi (0 : ℝ) from hr)
  have hFEvent : ∀ᶠ x in 𝓝 r, F x ≠ 0 :=
    (hFDiff r).continuousAt.eventually (eventually_ne_nhds hF)
  have hMEvent : ∀ᶠ x in 𝓝 r, profileM f F x ≠ 0 :=
    hMcont.eventually (eventually_ne_nhds hM)
  filter_upwards [hrEvent, hFEvent, hMEvent] with x hx hxF hxM
  exact etaFromFlux_eq_profileEta_at d f F x hx hxF hxM
    (hfDiff x) (hFDiff x)

/-- The third radial-flow equation derived from two profile ODEs and the
weighted Wronskian identity, in the integer dimensions `n=d+3≥3`.
It is exactly the equation required by `EtaBarrier.lean`. -/
theorem profileEta_flow_from_ODE
    (d : ℕ) (f F : ℝ → ℝ) (r f₁ F₁ f₂ F₂ : ℝ)
    (hr : 0 < r) (hFpos : 0 < F r)
    (hMpos : 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hode_f : radialODEAt ((d : ℝ) + 3) r (f r) f₁ f₂)
    (hode_F : radialODEAt ((d : ℝ) + 3) r (F r) F₁ F₂) :
    r * deriv (profileEta f F) r =
      profileK f F r * profileT F r ^ 2
      - (((d : ℝ) + 3) - 2 * profileY F r) * profileEta f F r
      - 2 * profileK f F r * profileEta f F r ^ 2 := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hMne : profileM f F r ≠ 0 := ne_of_gt hMpos
  have hode_f_div :
      f₂ + (((d + 1 : ℕ) : ℝ) + 1) / r * f₁
        - (((d + 1 : ℕ) : ℝ) + 1) / r ^ 2 * f r
        + (1 - (f r) ^ 2) * f r = 0 := by
    convert (radialODEAt_iff_divided ((d : ℝ) + 3) r
      (f r) f₁ f₂ hr).mp hode_f using 1
    push_cast
    ring
  have hode_F_div :
      F₂ + (((d + 1 : ℕ) : ℝ) + 1) / r * F₁
        - (((d + 1 : ℕ) : ℝ) + 1) / r ^ 2 * F r
        + (1 - (F r) ^ 2) * F r = 0 := by
    convert (radialODEAt_iff_divided ((d : ℝ) + 3) r
      (F r) F₁ F₂ hr).mp hode_F using 1
    push_cast
    ring
  have hJderiv := ratioFlux_hasDerivAt (d + 1) hrne
    hf hF hdf hdF hode_f_div hode_F_div
  have hJsource :
      r ^ (d + 2) * F r * f r * ((f r) ^ 2 - (F r) ^ 2) =
      r ^ (d + 2) * F r ^ 4 * profileK f F r *
        profileM f F r := by
    unfold profileM ratioM profileK
    field_simp [hFne]
  have hJ : HasDerivAt (ratioFlux (d + 2) f F)
      (r ^ (d + 2) * F r ^ 4 * profileK f F r *
        profileM f F r) r := by
    simpa only [hJsource] using hJderiv
  have hk := profileK_hasDerivAt f F r f₁ F₁ hf hF hFne
  let k₁ : ℝ := (f₁ * F r - f r * F₁) / F r ^ 2
  have hMderiv : HasDerivAt (profileM f F)
      (2 * profileK f F r * k₁) r := by
    simpa only [profileM, ratioM, k₁, Pi.pow_apply, Nat.reduceSub,
      pow_one, mul_assoc, mul_comm, mul_left_comm]
      using (hk.pow 2).sub_const 1
  have hEq := etaFromFlux_eq_profileEta_at d f F r hr hFne hMne
    (hfDiff r) (hFDiff r)
  have hMflow :
      r * (2 * profileK f F r * k₁) =
        2 * profileK f F r * profileM f F r *
          etaFromFlux d (ratioFlux (d + 2) f F) F
            (profileM f F) r := by
    calc
      r * (2 * profileK f F r * k₁) =
          r * deriv (profileM f F) r := by rw [hMderiv.deriv]
      _ = 2 * profileK f F r * profileM f F r *
          profileEta f F r := profileM_flow f F r f₁ F₁
            hf hF hFne hMne
      _ = _ := by rw [← hEq]
  have hcore := etaFromFlux_flow d (ratioFlux (d + 2) f F) F
    (profileM f F) r
    (r ^ (d + 2) * F r ^ 4 * profileK f F r * profileM f F r)
    F₁ (2 * profileK f F r * k₁) (profileK f F r)
    hr hFpos hMne hJ hF hMderiv rfl hMflow
  have hEvent := etaFromFlux_eventuallyEq_profileEta d f F r
    hr hFne hMne hfDiff hFDiff
  rw [hEvent.deriv_eq, hEq] at hcore
  simpa [profileT, profileY, hF.deriv] using hcore

/-- The same local profile hypotheses make the normalized ratio-growth
function differentiable.  This gives the `HasDerivAt` input required by the
first-contact barrier theorem. -/
theorem profileEta_differentiableAt_from_profiles
    (d : ℕ) (f F : ℝ → ℝ) (r f₁ F₁ f₂ F₂ : ℝ)
    (hr : 0 < r) (hFpos : 0 < F r)
    (hMpos : 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r) :
    DifferentiableAt ℝ (profileEta f F) r := by
  have hFne : F r ≠ 0 := ne_of_gt hFpos
  have hMne : profileM f F r ≠ 0 := ne_of_gt hMpos
  have hJdiff : DifferentiableAt ℝ (ratioFlux (d + 2) f F) r := by
    unfold ratioFlux
    exact ((hasDerivAt_pow (d + 2) r).differentiableAt.mul
      ((hF.differentiableAt.mul hdf.differentiableAt).sub
       (hf.differentiableAt.mul hdF.differentiableAt)))
  have hKdiff : DifferentiableAt ℝ (profileK f F) r :=
    (profileK_hasDerivAt f F r f₁ F₁ hf hF hFne).differentiableAt
  have hMdiff : DifferentiableAt ℝ (profileM f F) r := by
    exact (hKdiff.pow 2).sub_const 1
  have hDdiff : DifferentiableAt ℝ
      (fun x => x ^ (d + 1) * F x ^ 2 * profileM f F x) r := by
    exact ((hasDerivAt_pow (d + 1) r).differentiableAt.mul
      (hF.differentiableAt.pow 2)).mul hMdiff
  have hDne : r ^ (d + 1) * F r ^ 2 * profileM f F r ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (ne_of_gt hr)) (pow_ne_zero _ hFne)) hMne
  have hFluxDiff : DifferentiableAt ℝ
      (etaFromFlux d (ratioFlux (d + 2) f F) F (profileM f F)) r := by
    exact hJdiff.div hDdiff hDne
  have hEvent := etaFromFlux_eventuallyEq_profileEta d f F r
    hr hFne hMne hfDiff hFDiff
  exact hFluxDiff.congr_of_eventuallyEq hEvent.symm

/-- A convenient pair of hypotheses for `EtaBarrier`: an actual derivative
of `η` and the exact `η` flow at the same radius. -/
theorem profileEta_barrier_inputs
    (d : ℕ) (f F : ℝ → ℝ) (r f₁ F₁ f₂ F₂ : ℝ)
    (hr : 0 < r) (hFpos : 0 < F r)
    (hMpos : 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hode_f : radialODEAt ((d : ℝ) + 3) r (f r) f₁ f₂)
    (hode_F : radialODEAt ((d : ℝ) + 3) r (F r) F₁ F₂) :
    ∃ η₁ : ℝ,
      HasDerivAt (profileEta f F) η₁ r ∧
      r * η₁ = profileK f F r * profileT F r ^ 2
        - (((d : ℝ) + 3) - 2 * profileY F r) *
          profileEta f F r
        - 2 * profileK f F r * profileEta f F r ^ 2 := by
  refine ⟨deriv (profileEta f F) r, ?_, ?_⟩
  · exact (profileEta_differentiableAt_from_profiles d f F r
      f₁ F₁ f₂ F₂ hr hFpos hMpos hfDiff hFDiff hf hF hdf hdF).hasDerivAt
  · exact profileEta_flow_from_ODE d f F r f₁ F₁ f₂ F₂
      hr hFpos hMpos hfDiff hFDiff hf hF hdf hdF hode_f hode_F

/-- The ODE-level bridge into `EtaBarrier.eta_no_first_contact`.
The left-interval strict inequality is explicit: it must ultimately come
from a separate origin estimate and the choice of the first contact. -/
theorem profileEta_no_first_contact_from_ODE
    (d : ℕ) (f F : ℝ → ℝ) (a r f₁ F₁ f₂ F₂ : ℝ)
    (ha : a < r) (hr : 0 < r)
    (hleft : ∀ x, a < x → x < r →
      profileEta f F x < x / Real.sqrt 2)
    (hcontact : profileEta f F r = r / Real.sqrt 2)
    (hFpos : 0 < F r) (hFlt : F r < 1)
    (hkpos : 0 < profileK f F r)
    (hMpos : 0 < profileM f F r)
    (hylt : profileY F r < 1)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hf : HasDerivAt f f₁ r)
    (hF : HasDerivAt F F₁ r)
    (hdf : HasDerivAt (deriv f) f₂ r)
    (hdF : HasDerivAt (deriv F) F₂ r)
    (hode_f : radialODEAt ((d : ℝ) + 3) r (f r) f₁ f₂)
    (hode_F : radialODEAt ((d : ℝ) + 3) r (F r) F₁ F₂) : False := by
  obtain ⟨η₁, hder, hflow⟩ := profileEta_barrier_inputs d f F
    r f₁ F₁ f₂ F₂ hr hFpos hMpos hfDiff hFDiff
    hf hF hdf hdF hode_f hode_F
  have hν : (2 : ℝ) ≤ (d : ℝ) + 3 := by
    have hdnonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  exact eta_no_first_contact ha hr hleft hcontact hder
    hkpos hFpos hFlt hylt hν rfl hflow

end

end BrezisOP6
