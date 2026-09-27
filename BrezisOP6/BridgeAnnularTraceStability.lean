import BrezisOP6.RadialAnnularStability
import BrezisOP6.BridgeAnnularCoercivitySharp

/-!
# Annular trace distance from the exact quadratic bridge

The theorem below assembles the bridge's two coercive components.  Its
zero-mode hypothesis is an annular Picone estimate, as supplied by
`profilePicone_zero_mode_annular_l2_from_profiles` after the mean-to-Picone
integral identification.  The mean-zero derivative estimate is proved here
from the pointwise angular spectral gap and strict profile separation.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The nonnegative angular remainder makes the integral of the complete
quadratic bridge at least its one-dimensional mean integral. -/
theorem bridgeQuadratic_integral_ge_mean_integral
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (he : ‖e‖ = 1)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ d r)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc) volume 0 R) :
    (∫ r in (0 : ℝ)..R, bridgeMeanDensity m d c dc r) ≤
      ∫ r in (0 : ℝ)..R,
        bridgeQuadraticDensity m d v dv angular r := by
  have hdiff : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeQuadraticDensity m d v dv angular r -
        bridgeMeanDensity m d c dc r := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) R := by
      simpa only [uIcc_of_le hR] using hr
    exact bridgeQuadraticDensity_sub_mean_nonneg m e (v r) (dv r)
      r (d r) (c r) (dc r) (angular r) hr'.1
      (hd r hr') he (hv r hr') (hdv r hr') (hgap r hr')
  rw [intervalIntegral.integral_sub hfullInt hmeanInt] at hdiff
  linarith

/-- The exact quadratic bridge controls the entire annular `L²` distance
from the prescribed outer trace.  This statement needs an annular Picone
bound for `b=r c`; that bound is a theorem for the physical radial
profiles, not an independent positivity assumption. -/
theorem annular_trace_l2_controlled_by_quadratic_bridge
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc b : ℝ → ℝ) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (he : ‖e‖ = 1) (hcR : c R = 0)
    (hb : ∀ r ∈ Icc δ ρ, b r = r * c r)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ d r)
    (hdCont : ContinuousOn d (Icc δ R))
    (hdPos : ∀ r ∈ Icc δ R, 0 < d r)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc) volume 0 R)
    (hmeanNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m d c dc r)
    (hAlocal : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2)
        volume ε R)
    (hDNormInt : IntervalIntegrable
      (fun r => ‖dv r - dc r • e‖) volume δ R)
    (hDSqInt : IntervalIntegrable
      (fun r => ‖dv r - dc r • e‖ ^ 2) volume δ R)
    (hCInt : IntervalIntegrable (fun r => c r ^ 2) volume δ ρ)
    (hBInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hTraceInt : IntervalIntegrable
      (fun r => ‖v r - v R‖ ^ 2) volume δ ρ)
    (hTraceZeroInt : IntervalIntegrable
      (fun r => ‖(v R - c R • e) - (v r - c r • e)‖ ^ 2)
      volume δ ρ)
    (hTraceCont : ContinuousOn
      (fun r => v r - c r • e) (Icc δ R))
    (hTraceDeriv : ∀ r ∈ Ioo δ R,
      HasDerivAt (fun s => v s - c s • e)
        (dv r - dc r • e) r)
    (hPicone : ∃ lam : ℝ, 0 < lam ∧
      lam * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R, bridgeMeanDensity m d c dc r) :
    ∃ C : ℝ, 0 < C ∧
      (∫ r in δ..ρ, ‖v r - v R‖ ^ 2) ≤
        C * (∫ r in (0 : ℝ)..R,
          bridgeQuadraticDensity m d v dv angular r) := by
  have hMeanLe := bridgeQuadratic_integral_ge_mean_integral
    m e d v dv angular c dc R
    (hδ.le.trans (hδρ.trans hρR.le)) he hv hdv hd hgap
    hfullInt hmeanInt
  have hZero : ∃ lam : ℝ, 0 < lam ∧
      lam * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          bridgeQuadraticDensity m d v dv angular r := by
    obtain ⟨lam, hlam, hP⟩ := hPicone
    exact ⟨lam, hlam, hP.trans hMeanLe⟩
  have hRadial :=
    bridgeQuadratic_controls_meanZero_radial_derivative_on_annulus_sharp
      m e d v dv angular c dc δ R R hδ
      (hδρ.trans hρR.le) le_rfl he hv hdv hd hdCont hdPos hgap
      hfullInt hmeanInt hmeanNonneg hAlocal hDSqInt
  exact annular_trace_l2_of_zero_mode_and_radial_remainders
    e v (fun r => dv r - dc r • e) c b δ ρ R
    (∫ r in (0 : ℝ)..R, bridgeQuadraticDensity m d v dv angular r)
    hδ hδρ hρR.le he hcR hb hTraceCont hTraceDeriv
    hDNormInt hDSqInt hCInt hBInt hTraceInt hTraceZeroInt
    hZero hRadial

end

end BrezisOP6
