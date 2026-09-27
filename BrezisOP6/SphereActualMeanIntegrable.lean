import BrezisOP6.SphereMeanClosedProxyIntegrability
import BrezisOP6.SphereActualFluxIntegrable
import BrezisOP6.SphereFiniteMeanIntegrabilityTransfer

/-!
# Integrability of the actual finite-ball spherical mean

For a smooth competitor, the regularized mean is C¹ on a neighborhood of
the whole closed radius interval. The apparent singularity of the mean
density therefore cancels, and the actual L² mean density is integrable.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem finiteBallSphere_actual_meanDensity_intervalIntegrable_of_regularized
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin (m + 3))
    (hregular :
      let b := vectorSphereRadialMean (m + 3)
        (finiteBallSphereFamily (m + 3) R z)
        (fun s i => finiteBallSphereFamily_memLp
          (m + 3) R z hz s i) k
      IntervalIntegrable
        (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
          (fun s => b s / s)
          (fun s => deriv (fun t => b t / t) s))
        volume 0 R) :
    IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp
              (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R := by
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let b := vectorSphereRadialMean (m + 3) g hg k
  have hCoeff (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun s y => (g s y) k) (fun s => hg s k) r) =
        b r / r :=
    scalarSphereRadialMean_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k) r hr.1
  have hCoeffDeriv (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      sphereMeanCoefficient (m + 3) (dv r k) =
        deriv (fun s => b s / s) r :=
    scalarSphereRadialMean_deriv_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k)
      (dv r k) r hr.1
      (finiteBallSphereFamily_hasDerivAt_interior
        (m + 3) R z hz r hr k)
  have hRnull : ∀ᵐ r : ℝ ∂volume, r ≠ R := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      (measure_singleton R : volume {R} = 0)
  have hInterior : ∀ᵐ r : ℝ ∂volume.restrict (uIoc (0 : ℝ) R),
      r ∈ Ioo (0 : ℝ) R := by
    rw [uIoc_of_le hR.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hRnull] with r hr hrNe
    exact ⟨hr.1, lt_of_le_of_ne hr.2 hrNe⟩
  apply hregular.congr_ae
  filter_upwards [hInterior] with r hr
  change bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => b s / s)
      (fun s => deriv (fun t => b t / t) s) r =
    bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun t y => (g t y) k) (fun t => hg t k) s))
      (fun s => sphereMeanCoefficient (m + 3) (dv s k)) r
  simp only [bridgeMeanDensity, hCoeff r hr,
    hCoeffDeriv r hr]

theorem actual_finiteBallSphere_meanDensity_intervalIntegrable
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hu : ContDiff ℝ 1 u)
    (hHf0 : Hf 0 ≠ 0)
    (hf : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2))
    (hF : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2))
    (hfpos : ∀ r, 0 < r → r ≤ R → 0 < f r)
    (k : Fin (m + 3)) :
    let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
      fun x => (f ‖x‖)⁻¹ • u x
    let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      radialQuotient_contDiffOn_puncturedBall
        (m + 3) R f u hfC1 hfpos hu.contDiffOn
    IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
            (fun t => finiteBallSphereFamily_memLp
              (m + 3) R z hz t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k)))
      volume 0 R := by
  dsimp only
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos hu.contDiffOn
  let b : ℝ → ℝ := vectorSphereRadialMean (m + 3)
    (finiteBallSphereFamily (m + 3) R z)
    (fun s i => finiteBallSphereFamily_memLp
      (m + 3) R z hz s i) k
  let bproxy : ℝ → ℝ :=
    regularizedNumeratorSphereMean (m + 3) Hf u hu k
  let U : Set ℝ := {r | Hf (r ^ 2) ≠ 0}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_ne_fun
      (hHf.continuous.comp (continuous_id.pow 2))
      continuous_const
  have hUclosed : Icc (0 : ℝ) R ⊆ U := by
    intro r hr
    change Hf (r ^ 2) ≠ 0
    rcases eq_or_lt_of_le hr.1 with hzero | hrpos
    · subst r
      simpa using hHf0
    · intro hzero
      have hfr := hf r hrpos hr.2
      rw [hzero, mul_zero] at hfr
      exact (ne_of_gt (hfpos r hrpos hr.2)) hfr
  have hbproxy : ContDiffOn ℝ 1 bproxy U :=
    regularizedNumeratorSphereMean_contDiffOn_nonzero_set
      (m + 3) Hf u hHf hu k
  have hb (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      b r = bproxy r :=
    actual_finiteBallSphereRadialMean_eq_regularizedNumeratorMean
      (m + 3) R f Hf u hu hf hfpos hz k r hr hrR
  have hregular : IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => b s / s)
        (fun s => deriv (fun t => b t / t) s))
      volume 0 R :=
    bridgeMeanDensity_intervalIntegrable_of_closed_proxy
      m R f F Hf HF b bproxy hR U hUopen hUclosed hHf hHF
      hbproxy (fun r hr hrR => hf r hr hrR.le)
      (fun r hr hrR => hF r hr hrR.le) hb
  exact finiteBallSphere_actual_meanDensity_intervalIntegrable_of_regularized
    m f F R hR z hz k hregular

end

end BrezisOP6
