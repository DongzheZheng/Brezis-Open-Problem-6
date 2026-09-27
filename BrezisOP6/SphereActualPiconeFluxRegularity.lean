import BrezisOP6.ProfilePiconeFluxAnnulusRegularity
import BrezisOP6.SphereOuterMeanFluxContinuity
import BrezisOP6.EnergyQuotientPuncturedC1

/-!
# Actual Picone flux regularity on every positive annulus

Strict profile ordering keeps all Picone denominators away from zero on a
closed annulus. The smooth numerator supplies a C¹ regularized spherical
mean. These facts give the boundary-flux continuity and derivative
integrability required by the finite-ball Picone identity.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem actual_finiteBallSphere_profilePiconeFlux_annulus_regular
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F H : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC2 : ContDiff ℝ 2 f) (hFC2 : ContDiff ℝ 2 F)
    (hHC1 : ContDiff ℝ 1 H) (huGlobal : ContDiff ℝ 1 u)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r)
    (horder : ∀ r ∈ Ioc (0 : ℝ) R, F r < f r)
    (hfFactor : ∀ s : ℝ, 0 < s → s ≤ R →
      f s = s * H (s ^ 2))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (k : Fin (m + 3)) (δ : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R) :
    let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
      fun x => (f ‖x‖)⁻¹ • u x
    let hfpos' : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s :=
      fun s hs hsR => hfpos s ⟨hs, hsR⟩
    let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      radialQuotient_contDiffOn_puncturedBall
        (m + 3) R f u (hfC2.of_le (by norm_num)) hfpos'
          huGlobal.contDiffOn
    let b := vectorSphereRadialMean (m + 3)
      (finiteBallSphereFamily (m + 3) R z)
      (fun s i => finiteBallSphereFamily_memLp
        (m + 3) R z hz s i) k
    ContinuousOn (profilePiconeBoundaryFlux m f F b)
      (uIcc δ R) ∧
    IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b)) volume δ R := by
  dsimp only
  let hfC1 : ContDiff ℝ 1 f := hfC2.of_le (by norm_num)
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hfpos' : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s :=
    fun s hs hsR => hfpos s ⟨hs, hsR⟩
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos' huGlobal.contDiffOn
  let b : ℝ → ℝ := vectorSphereRadialMean (m + 3)
    (finiteBallSphereFamily (m + 3) R z)
    (fun s i => finiteBallSphereFamily_memLp
      (m + 3) R z hz s i) k
  let bproxy : ℝ → ℝ :=
    regularizedNumeratorSphereMean (m + 3) H u huGlobal k
  let U : Set ℝ :=
    (Ioi (0 : ℝ) ∩ {r | 0 < F r}) ∩
      ({r | 0 < f r ^ 2 - F r ^ 2} ∩ {r | H (r ^ 2) ≠ 0})
  have hUopen : IsOpen U := by
    have h1 : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
    have h2 : IsOpen {r : ℝ | 0 < F r} :=
      isOpen_Ioi.preimage hFC2.continuous
    have h3 : IsOpen {r : ℝ | 0 < f r ^ 2 - F r ^ 2} :=
      isOpen_Ioi.preimage
        ((hfC2.continuous.pow 2).sub (hFC2.continuous.pow 2))
    have h4 : IsOpen {r : ℝ | H (r ^ 2) ≠ 0} :=
      isOpen_ne_fun
        (hHC1.continuous.comp (continuous_id.pow 2))
        continuous_const
    exact (h1.inter h2).inter (h3.inter h4)
  have hUclosed : Icc δ R ⊆ U := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hδ hr.1
    have hrC : r ∈ Ioc (0 : ℝ) R := ⟨hrpos, hr.2⟩
    have hFr := hFpos r hrC
    have hfr := hfpos r hrC
    have hOr := horder r hrC
    have hsq : 0 < f r ^ 2 - F r ^ 2 := by nlinarith
    have hHne : H (r ^ 2) ≠ 0 := by
      intro hzero
      have hfactor := hfFactor r hrpos hr.2
      rw [hzero, mul_zero] at hfactor
      exact (ne_of_gt hfr) hfactor
    exact ⟨⟨hrpos, hFr⟩, ⟨hsq, hHne⟩⟩
  have hrposU (r : ℝ) (hr : r ∈ U) : 0 < r := hr.1.1
  have hFposU (r : ℝ) (hr : r ∈ U) : 0 < F r := hr.1.2
  have hMposU (r : ℝ) (hr : r ∈ U) :
      0 < profileM f F r := by
    have hFne : F r ≠ 0 := ne_of_gt (hFposU r hr)
    have hformula : profileM f F r =
        (f r ^ 2 - F r ^ 2) / F r ^ 2 := by
      unfold profileM ratioM profileK
      field_simp [hFne]
    rw [hformula]
    exact div_pos hr.2.1 (sq_pos_of_pos (hFposU r hr))
  have hbproxy : ContDiffOn ℝ 1 bproxy U := by
    apply (regularizedNumeratorSphereMean_contDiffOn_nonzero_set
      (m + 3) H u hHC1 huGlobal k).mono
    intro r hr
    exact hr.2.2
  have hb (r : ℝ) (hr : r ∈ Ioo δ R) : b r = bproxy r :=
    actual_finiteBallSphereRadialMean_eq_regularizedNumeratorMean
      (m + 3) R f H u huGlobal hfFactor hfpos' hz
      k r (hδ.trans hr.1) hr.2
  have hbCont : ContinuousOn b (Icc δ R) := by
    by_cases hδlt : δ < R
    · have htrace :=
        actual_quotient_finiteBallSphereFamily_trace_tendsto_outer_left
          (m + 3) R hR f u hfC1 hfpos'
          huGlobal.contDiffOn huBoundary k
      exact finiteBallSphereRadialMean_continuousOn_positive_annulus
        (m + 3) R δ hδ hδlt z hz k htrace
    · have hδEq : δ = R := le_antisymm hδR (le_of_not_gt hδlt)
      subst δ
      simpa only [Icc_self] using (continuousOn_singleton b R)
  exact profilePiconeBoundaryFlux_annulus_regular_of_C1_proxy
    m f F b bproxy δ R hδ hδR U hUopen hUclosed
    hfC2 hFC2 hrposU hFposU hMposU hbproxy hbCont hb

end

end BrezisOP6
