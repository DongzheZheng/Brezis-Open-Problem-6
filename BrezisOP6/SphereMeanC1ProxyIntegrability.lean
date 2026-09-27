import BrezisOP6.BridgeFluxC1Proxy
import BrezisOP6.SphereRadialGrowthIntegrability

/-!
# The spherical mean bridge has a removable radial singularity

The regularized mean b(r)=r·mean(z(rω)) may be continuous through the
origin even when the quotient z itself has a first-order pole.  If b has
a C¹ representative near zero and f,F have linear radial factors,
the apparent inverse powers in the mean bridge cancel algebraically.
The resulting density is r^m times a continuous function.
-/

namespace BrezisOP6

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

theorem bridgeMeanDensity_eq_regular_proxy
    (m : ℕ) (R δ r : ℝ)
    (f F Hf HF b bproxy : ℝ → ℝ)
    (hr : 0 < r) (hrδ : r < δ) (hδR : δ < R)
    (hbproxy : ContDiffOn ℝ 1 bproxy (Ioo (-δ) δ))
    (hf : ∀ s, 0 < s → s < R → f s = s * Hf (s ^ 2))
    (hF : ∀ s, 0 < s → s < R → F s = s * HF (s ^ 2))
    (hb : ∀ s, 0 < s → s < δ → b s = bproxy s) :
    bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => b s / s)
      (fun s => deriv (fun t => b t / t) s) r =
    r ^ m * (Hf (r ^ 2) ^ 2 - HF (r ^ 2) ^ 2) *
      ((r * deriv bproxy r - bproxy r) ^ 2 -
        (m + 2 : ℝ) * bproxy r ^ 2) := by
  have hnear : (fun t => b t / t) =ᶠ[𝓝 r]
      (fun t => bproxy t / t) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hr, hrδ⟩] with t ht
    rw [hb t ht.1 ht.2]
  have hbDiff : DifferentiableAt ℝ bproxy r := by
    have hrmem : r ∈ Ioo (-δ) δ := by
      constructor
      · linarith
      · exact hrδ
    exact (hbproxy.differentiableOn_one).differentiableAt
      (isOpen_Ioo.mem_nhds hrmem)
  have hderivProxy :
      deriv (fun t => bproxy t / t) r =
        (deriv bproxy r * r - bproxy r) / r ^ 2 := by
    have h :=
      (hbDiff.hasDerivAt.div (hasDerivAt_id r) (ne_of_gt hr)).deriv
    simpa only [Pi.div_apply, id_eq, mul_one] using h
  have hderiv :
      deriv (fun t => b t / t) r =
        (deriv bproxy r * r - bproxy r) / r ^ 2 := by
    rw [hnear.deriv_eq]
    exact hderivProxy
  rw [bridgeMeanDensity, hf r hr (hrδ.trans hδR),
    hF r hr (hrδ.trans hδR), hb r hr hrδ, hderiv]
  rw [pow_add]
  field_simp [ne_of_gt hr]

theorem bridgeMeanDensity_intervalIntegrable_of_C1_proxy
    (m : ℕ) (R δ : ℝ)
    (f F Hf HF b bproxy : ℝ → ℝ)
    (hδ : 0 < δ) (hδR : δ < R)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hbproxy : ContDiffOn ℝ 1 bproxy (Ioo (-δ) δ))
    (hf : ∀ s, 0 < s → s < R → f s = s * Hf (s ^ 2))
    (hF : ∀ s, 0 < s → s < R → F s = s * HF (s ^ 2))
    (hb : ∀ s, 0 < s → s < δ → b s = bproxy s)
    (houter : IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => b s / s)
        (fun s => deriv (fun t => b t / t) s))
      volume (δ / 2) R) :
    IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => b s / s)
        (fun s => deriv (fun t => b t / t) s))
      volume 0 R := by
  let Φ : ℝ → ℝ := fun r =>
    r ^ m * (Hf (r ^ 2) ^ 2 - HF (r ^ 2) ^ 2) *
      ((r * deriv bproxy r - bproxy r) ^ 2 -
        (m + 2 : ℝ) * bproxy r ^ 2)
  have hΦ : ContinuousOn Φ (Icc (0 : ℝ) (δ / 2)) := by
    have hderivCont : ContinuousOn (deriv bproxy)
        (Icc (0 : ℝ) (δ / 2)) := by
      apply (hbproxy.continuousOn_deriv_of_isOpen isOpen_Ioo
        (le_refl 1)).mono
      intro r hr
      constructor
      · linarith [hr.1]
      · linarith [hr.2]
    have hbCont : ContinuousOn bproxy
        (Icc (0 : ℝ) (δ / 2)) := by
      apply hbproxy.continuousOn.mono
      intro r hr
      constructor
      · linarith [hr.1]
      · linarith [hr.2]
    have hHfComp : ContinuousOn (fun r : ℝ => Hf (r ^ 2))
        (Icc (0 : ℝ) (δ / 2)) :=
      (hHf.continuous.comp (continuous_id.pow 2)).continuousOn
    have hHFComp : ContinuousOn (fun r : ℝ => HF (r ^ 2))
        (Icc (0 : ℝ) (δ / 2)) :=
      (hHF.continuous.comp (continuous_id.pow 2)).continuousOn
    dsimp [Φ]
    exact ((continuousOn_id.pow m).mul
      ((hHfComp.pow 2).sub (hHFComp.pow 2))).mul
      (((((continuousOn_id.mul hderivCont).sub hbCont).pow 2).sub
        ((continuousOn_const.mul (hbCont.pow 2)))))
  have hhalf : 0 ≤ δ / 2 := by positivity
  have hhalfδ : δ / 2 < δ := by linarith
  have hΦint : IntervalIntegrable Φ volume 0 (δ / 2) :=
    hΦ.intervalIntegrable_of_Icc hhalf
  have hinner : IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => b s / s)
        (fun s => deriv (fun t => b t / t) s))
      volume 0 (δ / 2) := by
    apply hΦint.congr
    rw [uIoc_of_le hhalf]
    intro r hr
    exact (bridgeMeanDensity_eq_regular_proxy m R δ r f F Hf HF b bproxy
      hr.1 (hr.2.trans_lt hhalfδ) hδR hbproxy hf hF hb).symm
  exact hinner.trans houter

end

end BrezisOP6
