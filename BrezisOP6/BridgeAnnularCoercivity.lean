import BrezisOP6.BridgeEqualityIntegral
import BrezisOP6.ZeroModeAnnularCoercivity

/-!
# Quantitative radial coercivity of the angular bridge

The smooth energy bridge has two nonnegative remainders.  Its first
remainder controls, on every compact interior annulus, the radial
derivative of the entire mean-zero spherical trace.  This is stronger
than a statement restricted to a prescribed harmonic degree: it includes
the degree-one radial variation and every higher harmonic at once.

The theorem controls derivatives.  Converting it into an `L²` distance
from the fixed outer trace requires a one-dimensional Hilbert-valued
Poincaré estimate, and passing it through Sobolev approximation requires
an appropriate trace/limit theorem.  Those steps are not claimed here.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact bridge remainder controls every mean-zero radial derivative
on a compact annulus.  The coefficient `κ` is obtained from the strict
profile gap and compactness, rather than supplied as an assumption. -/
theorem bridgeQuadratic_controls_meanZero_radial_derivative_on_annulus
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc : ℝ → ℝ) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ ≤ R)
    (he : ‖e‖ = 1)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ d r)
    (hdCont : ContinuousOn d (Icc δ ρ))
    (hdPos : ∀ r ∈ Icc δ ρ, 0 < d r)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc) volume 0 R)
    (hmeanNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m d c dc r)
    (hAInt : IntervalIntegrable
      (fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2)
      volume 0 R)
    (hNormInt : IntervalIntegrable
      (fun r => ‖dv r - dc r • e‖ ^ 2) volume δ ρ) :
    ∃ κ : ℝ, 0 < κ ∧
      κ * (∫ r in δ..ρ, ‖dv r - dc r • e‖ ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          bridgeQuadraticDensity m d v dv angular r := by
  let Q := bridgeQuadraticDensity m d v dv angular
  let M := bridgeMeanDensity m d c dc
  let A : ℝ → ℝ :=
    fun r => r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2
  let B : ℝ → ℝ :=
    fun r => r ^ m * d r *
      (angular r - (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2)
  have hR : 0 ≤ R := (le_of_lt hδ).trans (hδρ.trans hρR)
  have hpoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      Q r - M r = A r + B r := by
    have hp := bridgeQuadraticDensity_sub_mean_eq_remainder
      m e (v r) (dv r) r (d r) (c r) (dc r)
      (angular r) he (hv r hr) (hdv r hr)
    simpa only [Q, M, A, B, bridgeQuadraticDensity,
      bridgeMeanDensity] using hp
  have hBnonneg (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      0 ≤ B r := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (pow_nonneg hr.1 _) (hd r hr))
      (sub_nonneg.mpr (hgap r hr))
  have hApoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      A r ≤ Q r - M r := by
    linarith [hpoint r hr, hBnonneg r hr]
  have hAfull : (∫ r in (0 : ℝ)..R, A r) ≤
      ∫ r in (0 : ℝ)..R, Q r := by
    have hdiff : (∫ r in (0 : ℝ)..R, A r) ≤
        ∫ r in (0 : ℝ)..R, Q r - M r :=
      intervalIntegral.integral_mono_on hR hAInt
        (hfullInt.sub hmeanInt) hApoint
    rw [intervalIntegral.integral_sub hfullInt hmeanInt] at hdiff
    linarith
  have hAposAE : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) R)] A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hr.1.le _) (hd r ⟨hr.1.le, hr.2⟩))
      (sq_nonneg _)
  have hAannulus : (∫ r in δ..ρ, A r) ≤
      ∫ r in (0 : ℝ)..R, A r :=
    intervalIntegral.integral_mono_interval
      hδ.le hδρ hρR hAposAE hAInt
  have hwCont : ContinuousOn (fun r => r ^ (m + 2) * d r)
      (Icc δ ρ) :=
    (continuous_id.pow (m + 2)).continuousOn.mul hdCont
  have hwPos : ∀ r ∈ Icc δ ρ,
      0 < r ^ (m + 2) * d r := by
    intro r hr
    exact mul_pos (pow_pos (lt_of_lt_of_le hδ hr.1) _) (hdPos r hr)
  obtain ⟨κ, hκ, hκBound⟩ :=
    positive_continuous_annular_weight_has_lower_bound
      (fun r => r ^ (m + 2) * d r) δ ρ hδρ hwCont hwPos
  refine ⟨κ, hκ, ?_⟩
  have hASubInt : IntervalIntegrable A volume δ ρ := by
    apply hAInt.mono_set
    intro r hr
    have hr' : r ∈ Icc δ ρ := by
      simpa only [uIcc_of_le hδρ] using hr
    simpa only [uIcc_of_le hR] using
      (show r ∈ Icc (0 : ℝ) R from
        ⟨hδ.le.trans hr'.1, hr'.2.trans hρR⟩)
  have hScaledInt : IntervalIntegrable
      (fun r => κ * ‖dv r - dc r • e‖ ^ 2) volume δ ρ :=
    hNormInt.const_mul κ
  have hscaledPoint : ∀ r ∈ Icc δ ρ,
      κ * ‖dv r - dc r • e‖ ^ 2 ≤ A r := by
    intro r hr
    exact mul_le_mul_of_nonneg_right (hκBound r hr) (sq_nonneg _)
  have hLower : κ * (∫ r in δ..ρ,
      ‖dv r - dc r • e‖ ^ 2) ≤ ∫ r in δ..ρ, A r := by
    simpa only [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_mono_on hδρ hScaledInt hASubInt
        hscaledPoint)
  exact (hLower.trans hAannulus).trans hAfull

end

end BrezisOP6
