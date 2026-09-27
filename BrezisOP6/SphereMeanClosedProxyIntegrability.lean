import BrezisOP6.SphereMeanC1ProxyIntegrability

/-!
# The mean density for a closed-radius C¹ proxy

When the regularized radial mean has a C¹ representative on a neighborhood
of the whole physical radius interval, the algebraic cancellation at zero
and compact-interval continuity give integrability in a single step.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem bridgeMeanDensity_eq_closed_proxy
    (m : ℕ) (R r : ℝ)
    (f F Hf HF b bproxy : ℝ → ℝ)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hbproxy : ContDiffOn ℝ 1 bproxy U)
    (hr : 0 < r) (hrR : r < R) (hrU : r ∈ U)
    (hf : ∀ s, 0 < s → s < R → f s = s * Hf (s ^ 2))
    (hF : ∀ s, 0 < s → s < R → F s = s * HF (s ^ 2))
    (hb : ∀ s, 0 < s → s < R → b s = bproxy s) :
    bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => b s / s)
      (fun s => deriv (fun t => b t / t) s) r =
    r ^ m * (Hf (r ^ 2) ^ 2 - HF (r ^ 2) ^ 2) *
      ((r * deriv bproxy r - bproxy r) ^ 2 -
        (m + 2 : ℝ) * bproxy r ^ 2) := by
  have hnear : (fun t => b t / t) =ᶠ[𝓝 r]
      (fun t => bproxy t / t) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hr, hrR⟩] with t ht
    rw [hb t ht.1 ht.2]
  have hbDiff : DifferentiableAt ℝ bproxy r :=
    (hbproxy.differentiableOn_one).differentiableAt
      (hUopen.mem_nhds hrU)
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
  rw [bridgeMeanDensity, hf r hr hrR, hF r hr hrR,
    hb r hr hrR, hderiv]
  rw [pow_add]
  field_simp [ne_of_gt hr]

theorem bridgeMeanDensity_intervalIntegrable_of_closed_proxy
    (m : ℕ) (R : ℝ)
    (f F Hf HF b bproxy : ℝ → ℝ)
    (hR : 0 < R)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hUclosed : Icc (0 : ℝ) R ⊆ U)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hbproxy : ContDiffOn ℝ 1 bproxy U)
    (hf : ∀ s, 0 < s → s < R → f s = s * Hf (s ^ 2))
    (hF : ∀ s, 0 < s → s < R → F s = s * HF (s ^ 2))
    (hb : ∀ s, 0 < s → s < R → b s = bproxy s) :
    IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => b s / s)
        (fun s => deriv (fun t => b t / t) s))
      volume 0 R := by
  let Φ : ℝ → ℝ := fun r =>
    r ^ m * (Hf (r ^ 2) ^ 2 - HF (r ^ 2) ^ 2) *
      ((r * deriv bproxy r - bproxy r) ^ 2 -
        (m + 2 : ℝ) * bproxy r ^ 2)
  have hderivCont : ContinuousOn (deriv bproxy) (Icc (0 : ℝ) R) :=
    (hbproxy.continuousOn_deriv_of_isOpen hUopen
      (le_refl 1)).mono hUclosed
  have hbCont : ContinuousOn bproxy (Icc (0 : ℝ) R) :=
    hbproxy.continuousOn.mono hUclosed
  have hHfComp : ContinuousOn (fun r : ℝ => Hf (r ^ 2))
      (Icc (0 : ℝ) R) :=
    (hHf.continuous.comp (continuous_id.pow 2)).continuousOn
  have hHFComp : ContinuousOn (fun r : ℝ => HF (r ^ 2))
      (Icc (0 : ℝ) R) :=
    (hHF.continuous.comp (continuous_id.pow 2)).continuousOn
  have hΦ : ContinuousOn Φ (Icc (0 : ℝ) R) := by
    dsimp [Φ]
    exact ((continuousOn_id.pow m).mul
      ((hHfComp.pow 2).sub (hHFComp.pow 2))).mul
      (((((continuousOn_id.mul hderivCont).sub hbCont).pow 2).sub
        ((continuousOn_const.mul (hbCont.pow 2)))))
  have hΦint : IntervalIntegrable Φ volume 0 R :=
    hΦ.intervalIntegrable_of_Icc hR.le
  apply hΦint.congr_ae
  rw [uIoc_of_le hR.le, ← restrict_Ioo_eq_restrict_Ioc]
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro r hr
  exact (bridgeMeanDensity_eq_closed_proxy m R r f F Hf HF b bproxy
    U hUopen hbproxy hr.1 hr.2 (hUclosed ⟨hr.1.le, hr.2.le⟩)
    hf hF hb).symm

end

end BrezisOP6
