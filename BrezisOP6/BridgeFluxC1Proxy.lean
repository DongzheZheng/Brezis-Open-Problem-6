import BrezisOP6.BridgePiconeIdentification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrability of the origin flux through a removable C¹ representative

The spherical zero mode used by the finite-ball construction is totalized
at radius zero.  It need not be continuous there.  On positive radii it
agrees with a regular mean coefficient.  The flux has an integrable
derivative whenever that regular coefficient has a C¹ representative.
The one-point mismatch at the origin has no effect on interval
integrability.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

/-- The positive-radius factorization of the Picone weight. -/
theorem piconeWeightFromProfiles_eq_factor
    (f F Hf HF : ℝ → ℝ) (R r : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ s, 0 < s → s < R → f s = s * Hf (s ^ 2))
    (hF : ∀ s, 0 < s → s < R → F s = s * HF (s ^ 2)) :
    piconeWeightFromProfiles f F r =
      Hf (r ^ 2) ^ 2 - HF (r ^ 2) ^ 2 := by
  rw [piconeWeightFromProfiles, hf r hr hrR, hF r hr hrR]
  field_simp [ne_of_gt hr]

/-- A C¹ representative of the regularized spherical mean removes the
apparent singularity in the zero-mode flux. -/
theorem bridgeOriginFlux_deriv_intervalIntegrable_of_C1_proxy
    (m : ℕ) (R δ : ℝ) (f F Hf HF b bproxy : ℝ → ℝ)
    (hδ : 0 < δ) (hδR : δ < R)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hbproxy : ContDiffOn ℝ 1 bproxy (Ioo (-δ) δ))
    (hf : ∀ s, 0 < s → s < R → f s = s * Hf (s ^ 2))
    (hF : ∀ s, 0 < s → s < R → F s = s * HF (s ^ 2))
    (hb : ∀ s, 0 < s → s < δ → b s = bproxy s)
    (houter : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume (δ / 2) R) :
    IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume 0 R := by
  let Φ : ℝ → ℝ := fun r =>
    r ^ (m + 1) *
      (Hf (r ^ 2) ^ 2 - HF (r ^ 2) ^ 2) *
      bproxy r ^ 2
  have hΦ : ContDiffOn ℝ 1 Φ (Ioo (-δ) δ) := by
    dsimp [Φ]
    fun_prop
  have hhalf : 0 ≤ δ / 2 := by positivity
  have hhalfδ : δ / 2 < δ := by linarith
  have hΦint : IntervalIntegrable (deriv Φ) volume 0 (δ / 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hhalf
    apply (hΦ.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono
    intro r hr
    exact ⟨by linarith [hr.1], hr.2.trans_lt hhalfδ⟩
  have hinner : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume 0 (δ / 2) := by
    apply hΦint.congr
    rw [uIoc_of_le hhalf]
    intro r hr
    have hrδ : r < δ := lt_of_le_of_lt hr.2 hhalfδ
    have hlocal :
        bridgeOriginFlux m f F b =ᶠ[nhds r] Φ := by
      have hopen : IsOpen (Ioo (0 : ℝ) δ) := isOpen_Ioo
      filter_upwards [hopen.mem_nhds ⟨hr.1, hrδ⟩] with s hs
      dsimp [Φ, bridgeOriginFlux]
      rw [piconeWeightFromProfiles_eq_factor
        f F Hf HF R s hs.1 (hs.2.trans hδR) hf hF,
        hb s hs.1 hs.2]
    exact hlocal.deriv_eq.symm
  exact hinner.trans houter

/-- The closed-interval form: a C¹ proxy on any open neighborhood of
the whole physical radius interval gives integrability without a separate
annular hypothesis.  The derivative at the artificial outer endpoint
is ignored, as it is a Lebesgue-null point. -/
theorem bridgeOriginFlux_deriv_intervalIntegrable_of_closed_proxy
    (m : ℕ) (R : ℝ) (f F Hf HF b bproxy : ℝ → ℝ)
    (hR : 0 < R)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hUclosed : Icc (0 : ℝ) R ⊆ U)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hbproxy : ContDiffOn ℝ 1 bproxy U)
    (hf : ∀ s, 0 < s → s < R → f s = s * Hf (s ^ 2))
    (hF : ∀ s, 0 < s → s < R → F s = s * HF (s ^ 2))
    (hb : ∀ s, 0 < s → s < R → b s = bproxy s) :
    IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume 0 R := by
  let Φ : ℝ → ℝ := fun r =>
    r ^ (m + 1) *
      (Hf (r ^ 2) ^ 2 - HF (r ^ 2) ^ 2) *
      bproxy r ^ 2
  have hΦ : ContDiffOn ℝ 1 Φ U := by
    dsimp [Φ]
    fun_prop
  have hΦint : IntervalIntegrable (deriv Φ) volume 0 R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hR.le
    exact (hΦ.continuousOn_deriv_of_isOpen hUopen (le_refl 1)).mono hUclosed
  apply hΦint.congr_ae
  rw [uIoc_of_le hR.le, ← restrict_Ioo_eq_restrict_Ioc]
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro r hr
  have hlocal :
      bridgeOriginFlux m f F b =ᶠ[nhds r] Φ := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    dsimp [Φ, bridgeOriginFlux]
    rw [piconeWeightFromProfiles_eq_factor
      f F Hf HF R s hs.1 hs.2 hf hF, hb s hs.1 hs.2]
  exact hlocal.deriv_eq.symm

end

end BrezisOP6
