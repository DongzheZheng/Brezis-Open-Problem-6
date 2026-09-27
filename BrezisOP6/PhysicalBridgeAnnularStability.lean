import BrezisOP6.BridgeAnnularTraceStability
import BrezisOP6.BridgeMeanPiconeQuantitative
import BrezisOP6.BridgeAnnularLocalIntegrability
import BrezisOP6.AnnularWeightedSquareIntegrability

/-!
# Annular bridge stability for physical radial profiles

The public radial data imply the strict profile gap and the quantitative
Picone estimate for the scalar mean.  These are inserted into the exact
angular bridge.  The remaining assumptions describe regularity and
integrability of an actual sphere-valued trace; they do not include a
positivity or coercivity assumption.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A physical profile pair turns the two nonnegative bridge remainders
into quantitative `L²` control of a spherical trace on a compact annulus.
The scalar Picone coercivity and the strict profile gap are consequences
of `PhysicalRadialData`; the listed trace conditions are analytic facts
to be supplied for the particular smooth competitor. -/
theorem PhysicalRadialData.annular_trace_l2_controlled_by_bridge
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (e : H) (v dv : ℝ → H) (angular c dc b db : ℝ → ℝ)
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (he : ‖e‖ = 1) (hcR : c R = 0)
    (hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m
        (fun r => p.f r ^ 2 - p.F r ^ 2) v dv angular) volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m
        (fun r => p.f r ^ 2 - p.F r ^ 2) c dc) volume 0 R)
    (hdvCont : ContinuousOn dv (Ioo (0 : ℝ) R))
    (hdcCont : ContinuousOn dc (Ioo (0 : ℝ) R))
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
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hc : ∀ r ∈ Ioo (0 : ℝ) R, c r = b r / r)
    (hdc : ∀ r ∈ Ioo (0 : ℝ) R,
      dc r = deriv (fun s => b s / s) r)
    (hDint : IntervalIntegrable
      (profilePiconeDensity m p.f p.F b db) volume 0 R)
    (hPicFluxCont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m p.f p.F b)
        (uIcc ε R))
    (hPicFluxInt : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m p.f p.F b))
        volume ε R)
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B))
    (hFluxCont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (bridgeOriginFlux m p.f p.F b) (uIcc ε R))
    (hFluxLim : Tendsto (bridgeOriginFlux m p.f p.F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hFluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m p.f p.F b)) volume 0 R) :
    ∃ C : ℝ, 0 < C ∧
      (∫ r in δ..ρ, ‖v r - v R‖ ^ 2) ≤
        C * (∫ r in (0 : ℝ)..R,
          bridgeQuadraticDensity m
            (fun r => p.f r ^ 2 - p.F r ^ 2)
            v dv angular r) := by
  have hd : ∀ r ∈ Icc (0 : ℝ) R,
      0 ≤ p.f r ^ 2 - p.F r ^ 2 := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hr0 | hrpos
    · subst r
      simp [p.hf0, p.hF0]
    · exact (p.profile_gap_positive m R r ⟨hrpos, hr.2⟩).le
  have hdCont : ContinuousOn
      (fun r => p.f r ^ 2 - p.F r ^ 2) (Icc δ R) :=
    ((p.hfC2.continuous.pow 2).sub (p.hFC2.continuous.pow 2)).continuousOn
  have hdPos : ∀ r ∈ Icc δ R,
      0 < p.f r ^ 2 - p.F r ^ 2 := by
    intro r hr
    exact p.profile_gap_positive m R r
      ⟨lt_of_lt_of_le hδ hr.1, hr.2⟩
  have hdContOpen : ContinuousOn
      (fun r => p.f r ^ 2 - p.F r ^ 2) (Ioo (0 : ℝ) R) :=
    ((p.hfC2.continuous.pow 2).sub (p.hFC2.continuous.pow 2)).continuousOn
  have hAlocal := bridgeRadialRemainder_intervalIntegrable_of_full_and_mean
    m e (fun r => p.f r ^ 2 - p.F r ^ 2) v dv angular c dc R
    p.hR he hv hdv hd hgap hdContOpen hdvCont hdcCont
    hfullInt hmeanInt
  have hδR : δ ≤ R := hδρ.trans hρR.le
  have hWeightCont : ContinuousOn
      (fun r => r ^ (m + 2) * (p.f r ^ 2 - p.F r ^ 2))
      (Icc δ R) :=
    (continuousOn_id.pow (m + 2)).mul hdCont
  have hWeightPos : ∀ r ∈ Icc δ R,
      0 < r ^ (m + 2) * (p.f r ^ 2 - p.F r ^ 2) := by
    intro r hr
    exact mul_pos (pow_pos (lt_of_lt_of_le hδ hr.1) _) (hdPos r hr)
  obtain ⟨κ, hκ, hκBound⟩ :=
    positive_continuous_annular_weight_has_lower_bound
      (fun r => r ^ (m + 2) * (p.f r ^ 2 - p.F r ^ 2))
      δ R hδR hWeightCont hWeightPos
  have hDCont : ContinuousOn
      (fun r => dv r - dc r • e) (Ioo δ R) := by
    have hsub : Ioo δ R ⊆ Ioo (0 : ℝ) R := by
      intro r hr
      exact ⟨hδ.trans hr.1, hr.2⟩
    exact (hdvCont.mono hsub).sub
      ((hdcCont.mono hsub).smul continuousOn_const)
  have hDSqMeas : AEStronglyMeasurable
      (fun r => ‖dv r - dc r • e‖ ^ 2)
      (volume.restrict (Ioc δ R)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact (hDCont.norm.pow 2).aestronglyMeasurable measurableSet_Ioo
  have hDSqInt : IntervalIntegrable
      (fun r => ‖dv r - dc r • e‖ ^ 2) volume δ R :=
    annular_square_intervalIntegrable_of_weighted
      (fun r => r ^ (m + 2) * (p.f r ^ 2 - p.F r ^ 2))
      (fun r => ‖dv r - dc r • e‖) δ R κ hδR hκ
      hκBound (hAlocal δ hδ hδR) hDSqMeas
  have hDNormMeas : AEStronglyMeasurable
      (fun r => |‖dv r - dc r • e‖|)
      (volume.restrict (Ioc δ R)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact (hDCont.norm.abs).aestronglyMeasurable measurableSet_Ioo
  have hDNormInt : IntervalIntegrable
      (fun r => ‖dv r - dc r • e‖) volume δ R := by
    have hAbs := annular_abs_intervalIntegrable_of_square
      (fun r => ‖dv r - dc r • e‖) δ R hδR hDSqInt hDNormMeas
    simpa only [abs_of_nonneg (norm_nonneg _)] using hAbs
  have hbAnn : ∀ r ∈ Icc δ ρ, b r = r * c r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hδ hr.1
    have hrInt : r ∈ Ioo (0 : ℝ) R :=
      ⟨hrpos, lt_of_le_of_lt hr.2 hρR⟩
    rw [hc r hrInt]
    field_simp [ne_of_gt hrpos]
  obtain ⟨lam, hlam, hPicone⟩ := p.bridgeMean_annular_l2
    m R b db c dc δ ρ hδ hδρ hρR hb hbR hc hdc
    hDint hBInt hPicFluxCont hPicFluxInt hblim
    hFluxCont hFluxLim hFluxInt
  have hBnonneg : 0 ≤ ∫ r in δ..ρ, b r ^ 2 :=
    intervalIntegral.integral_nonneg hδρ
      (fun r _ => sq_nonneg (b r))
  have hmeanNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m
        (fun r => p.f r ^ 2 - p.F r ^ 2) c dc r := by
    nlinarith [mul_nonneg hlam.le hBnonneg]
  exact annular_trace_l2_controlled_by_quadratic_bridge
    m e (fun r => p.f r ^ 2 - p.F r ^ 2) v dv angular c dc b
    δ ρ R hδ hδρ hρR he hcR hbAnn hv hdv hd hdCont hdPos
    hgap hfullInt hmeanInt hmeanNonneg hAlocal hDNormInt hDSqInt
    hCInt hBInt hTraceInt hTraceZeroInt hTraceCont hTraceDeriv
    ⟨lam, hlam, hPicone⟩

end

end BrezisOP6
