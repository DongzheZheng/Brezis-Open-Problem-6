import BrezisOP6.SphereActualC1Proxy
import BrezisOP6.EnergyQuotientPuncturedC1

/-!
# Actual zero-mode flux integrability

For a smooth competitor, the regularized spherical mean has a C¹
representative on an open neighborhood of the entire closed radius
interval.  The finite-ball family's totalization at zero and beyond the
outer sphere changes the derivative only at the two endpoints, which
have zero Lebesgue measure.
-/

namespace BrezisOP6

open MeasureTheory Set Metric

noncomputable section

theorem actual_finiteBallSphere_bridgeOriginFlux_deriv_intervalIntegrable
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
      (deriv (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R z)
          (fun s i => finiteBallSphereFamily_memLp
            (m + 3) R z hz s i) k))) volume 0 R := by
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
  exact bridgeOriginFlux_deriv_intervalIntegrable_of_closed_proxy
    m R f F Hf HF b bproxy hR U hUopen hUclosed hHf hHF
    hbproxy (fun r hr hrR => hf r hr hrR.le)
    (fun r hr hrR => hF r hr hrR.le) hb

end

end BrezisOP6
