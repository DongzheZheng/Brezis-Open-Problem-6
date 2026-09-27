import BrezisOP6.ProfilePiconeFluxC1Proxy
import BrezisOP6.BridgeFluxC1Proxy

/-!
# Picone flux regularity from a C¹ radial mean proxy

The physical zero mode can be totalized outside the ball. On the open
annulus it agrees with a C¹ proxy; at the outer sphere it has a continuous
left trace. The Picone flux is therefore continuous on the closed annulus,
and its derivative is integrable there without any derivative at `R`.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem profilePiconeBoundaryFlux_annulus_regular_of_C1_proxy
    (m : ℕ) (f F b bproxy : ℝ → ℝ)
    (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hUclosed : Icc δ R ⊆ U)
    (hfC2 : ContDiff ℝ 2 f) (hFC2 : ContDiff ℝ 2 F)
    (hrpos : ∀ r ∈ U, 0 < r)
    (hFpos : ∀ r ∈ U, 0 < F r)
    (hMpos : ∀ r ∈ U, 0 < profileM f F r)
    (hbproxy : ContDiffOn ℝ 1 bproxy U)
    (hbCont : ContinuousOn b (Icc δ R))
    (hb : ∀ r ∈ Ioo δ R, b r = bproxy r) :
    ContinuousOn (profilePiconeBoundaryFlux m f F b)
      (uIcc δ R) ∧
    IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b)) volume δ R := by
  have hFactor : ContDiffOn ℝ 1
      (profilePiconeOriginFactor f F) U :=
    profilePiconeOriginFactor_contDiffOn f F U hUopen hfC2 hFC2
      (fun r hr => ne_of_gt (hrpos r hr))
      (fun r hr => ne_of_gt (hFpos r hr))
      (fun r hr => ne_of_gt (hMpos r hr))
  have hFactorCont : ContinuousOn (profilePiconeOriginFactor f F)
      (Icc δ R) := hFactor.continuousOn.mono hUclosed
  have hEq (r : ℝ) (hr : r ∈ Icc δ R) :
      profilePiconeBoundaryFlux m f F b r =
        r ^ (m + 1) * profilePiconeOriginFactor f F r * b r ^ 2 := by
    have hU := hUclosed hr
    exact profilePiconeBoundaryFlux_eq_origin_form m f F b r
      (ne_of_gt (piconeMultiplier_pos f F r
        (hrpos r hU) (hFpos r hU) (hMpos r hU)))
  have hFluxCont : ContinuousOn
      (profilePiconeBoundaryFlux m f F b) (Icc δ R) := by
    have hProxyCont : ContinuousOn
        (fun r => r ^ (m + 1) *
          profilePiconeOriginFactor f F r * b r ^ 2)
        (Icc δ R) :=
      ((continuousOn_id.pow (m + 1)).mul hFactorCont).mul
        (hbCont.pow 2)
    exact hProxyCont.congr (fun r hr => hEq r hr)
  let Φ : ℝ → ℝ := fun r =>
    r ^ (m + 1) * profilePiconeOriginFactor f F r * bproxy r ^ 2
  have hΦ : ContDiffOn ℝ 1 Φ U := by
    dsimp [Φ]
    exact ((contDiffOn_id.pow (m + 1)).mul hFactor).mul
      (hbproxy.pow 2)
  have hDerivΦInt : IntervalIntegrable (deriv Φ) volume δ R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hδR
    exact (hΦ.continuousOn_deriv_of_isOpen hUopen
      (le_refl 1)).mono hUclosed
  have hDerivInt : IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b))
      volume δ R := by
    apply hDerivΦInt.congr_ae
    rw [uIoc_of_le hδR, ← restrict_Ioo_eq_restrict_Ioc]
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro r hr
    have hlocal : profilePiconeBoundaryFlux m f F b =ᶠ[𝓝 r] Φ := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
      have hsU : s ∈ U := hUclosed ⟨hs.1.le, hs.2.le⟩
      rw [hEq s ⟨hs.1.le, hs.2.le⟩, hb s hs]
    exact hlocal.deriv_eq.symm
  exact ⟨by simpa only [uIcc_of_le hδR] using hFluxCont,
    hDerivInt⟩

end

end BrezisOP6
