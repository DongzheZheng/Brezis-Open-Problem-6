import BrezisOP6.PhysicalBridgeAnnularStability
import BrezisOP6.SphereTraceAnnularContinuity
import BrezisOP6.ActualModeCertificate
import BrezisOP6.SphereActualPiconeFluxRegularity
import BrezisOP6.SphereActualFluxRightLimit
import BrezisOP6.SphereOuterMeanFluxContinuity
import BrezisOP6.SphereFiniteMeanIntegrabilityTransfer
import BrezisOP6.SphereFiniteFamilyGap
import BrezisOP6.SphereBoundaryMeanZero

/-!
# Actual smooth finite-ball coordinate: quantitative annular stability

All analytic inputs to the physical one-coordinate bridge are obtained
from a genuine smooth fixed-trace competitor and the two radial profiles.
The one-dimensional constant depends only on the profiles and the chosen
annulus; its existential formulation can be combined over finitely many
target coordinates.
-/

namespace BrezisOP6

open Filter MeasureTheory Set Metric
open scoped Topology

noncomputable section

theorem actual_smooth_annular_coordinate_stability
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hu : SmoothBallCompetitor m R p.f u)
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (k : Fin (m + 3)) :
    let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
      fun x => (p.f ‖x‖)⁻¹ • u x
    let hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
    let hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < p.f s :=
      fun s hs hsR => p.hfpos s ⟨hs, hsR⟩
    let hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      radialQuotient_contDiffOn_puncturedBall
        (m + 3) R p.f u hfC1 hfpos hu.1.contDiffOn
    let g := finiteBallSphereFamily (m + 3) R z
    let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
    let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
    let v := scalarSphereFamilyTrace (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k)
    ∃ C : ℝ, 0 < C ∧
      (∫ r in δ..ρ, ‖v r - v R‖ ^ 2) ≤
        C * (∫ r in (0 : ℝ)..R,
          scalarSphereBridgeDensity m p.f p.F
            (fun s y => (g s y) k)
            (fun s => hg s k) (fun s => dv s k) r) := by
  dsimp only
  have hfC1 : ContDiff ℝ 1 p.f := p.hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 p.F := p.hFC2.of_le (by norm_num)
  have hdfC1 : ContDiff ℝ 1 (deriv p.f) :=
    radial_profile_deriv_contDiff_one p.f p.hfC2
  have hfDiff : Differentiable ℝ p.f :=
    fun r => hfC1.differentiable_one r
  have hFDiff : Differentiable ℝ p.F :=
    fun r => hFC1.differentiable_one r
  have hHf0 : p.Hf 0 ≠ 0 := by
    rw [p.hHf0]
    exact ne_of_gt p.hβ
  have hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < p.f s :=
    fun s hs hsR => p.hfpos s ⟨hs, hsR⟩
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (p.f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R p.f u hfC1 hfpos hu.1.contDiffOn
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s i => finiteBallSphereFamily_memLp (m + 3) R z hz s i
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  let v := scalarSphereFamilyTrace (m + 3)
    (fun s y => (g s y) k) (fun s => hg s k)
  let c : ℝ → ℝ := fun r => sphereMeanCoefficient (m + 3) (v r)
  let dc : ℝ → ℝ := fun r => sphereMeanCoefficient (m + 3) (dv r k)
  let b : ℝ → ℝ := vectorSphereRadialMean (m + 3) g hg k
  let e := unitSphereConstant (m + 3)
  let angular : ℝ → ℝ :=
    fun r => unitSphereAngularEnergy (m + 3) (fun y => (g r y) k)
  have he : ‖e‖ = 1 := unitSphereConstant_norm (m + 3) (by omega)
  have hbR : b R = 0 :=
    vectorSphereRadialMean_boundary_zero_of_identity_family
      (m + 3) R (unitSphereCoordinateMeanZero_actual (m + 3))
      g hg (fun ω => finiteBallSphereFamily_outer (m + 3) R z ω) k
  have hcR : c R = 0 := by
    have hmul : R * c R = 0 := by
      simpa only [b, vectorSphereRadialMean,
        scalarSphereRadialMean, c, v] using hbR
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt p.hR)
  have hv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (v r - c r • e) e = 0 := by
    intro r _
    exact sphereMeanZeroPart_orthogonal (m + 3) (v r) he
  have hdv : ∀ r ∈ Icc (0 : ℝ) R,
      inner ℝ (dv r k - dc r • e) e = 0 := by
    intro r _
    exact sphereMeanZeroPart_orthogonal (m + 3) (dv r k) he
  have hgap : ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r :=
    finiteBallSphereFamily_angular_gap m hLocal R p.hR z hz k
  have hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m
        (fun r => p.f r ^ 2 - p.F r ^ 2)
        v (fun r => dv r k) angular) volume 0 R := by
    simpa only [scalarSphereBridgeDensity] using
      (actual_finiteBall_scalarBridge_intervalIntegrable
        m R p.hR p.f p.F p.Hf u hfC1 hdfC1 hFC1 p.hHf
        hu.1 hHf0 p.hfFactor hfpos
        (fun r hr => (p.profile_gap_positive m R r
          ⟨hr.1, hr.2.le⟩).le) k)
  have hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m
        (fun r => p.f r ^ 2 - p.F r ^ 2) c dc) volume 0 R := by
    simpa only [c, dc, v, g, hg, dv] using
      (actual_finiteBallSphere_meanDensity_intervalIntegrable
        m R p.hR p.f p.F p.Hf p.HF u hfC1 p.hHf p.hHF
        hu.1 hHf0 p.hfFactor p.hFFactor hfpos k)
  have hFluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m p.f p.F b)) volume 0 R := by
    simpa only [b, g, hg] using
      (actual_finiteBallSphere_bridgeOriginFlux_deriv_intervalIntegrable
        m R p.hR p.f p.F p.Hf p.HF u hfC1 p.hHf p.hHF
        hu.1 hHf0 p.hfFactor p.hFFactor hfpos k)
  have hDint : IntervalIntegrable
      (profilePiconeDensity m p.f p.F b (deriv b)) volume 0 R :=
    finiteBallSphere_profilePiconeDensity_intervalIntegrable
      m p.f p.F R p.hR z hz hfDiff hFDiff k hmeanInt hFluxInt
  have hTraceLim : Tendsto v (𝓝[<] R) (𝓝 (v R)) := by
    simpa only [v, g, hg] using
      (actual_quotient_finiteBallSphereFamily_trace_tendsto_outer_left
        (m + 3) R p.hR p.f u hfC1 hfpos
        hu.1.contDiffOn hu.2 k)
  have hvCont : ContinuousOn v (Icc δ R) :=
    finiteBallSphereFamily_trace_continuousOn_positive_annulus
      (m + 3) R δ hδ (lt_of_le_of_lt hδρ hρR)
      z hz k hTraceLim
  have hMeanCont : Continuous (sphereMeanCoefficient (m + 3)) := by
    unfold sphereMeanCoefficient
    fun_prop
  have hcCont : ContinuousOn c (Icc δ R) :=
    hMeanCont.comp_continuousOn hvCont
  have hdvCont : ContinuousOn (fun r => dv r k) (Ioo (0 : ℝ) R) :=
    finiteBallSphereFamilyRadialL2_continuousOn (m + 3) R z hz k
  have hdcCont : ContinuousOn dc (Ioo (0 : ℝ) R) :=
    hMeanCont.comp_continuousOn hdvCont
  have hδR : δ ≤ R := hδρ.trans hρR.le
  have hsub : Icc δ ρ ⊆ Icc δ R := by
    intro r hr
    exact ⟨hr.1, hr.2.trans hρR.le⟩
  have hCInt : IntervalIntegrable (fun r => c r ^ 2) volume δ ρ :=
    (by
      simpa only [uIcc_of_le hδρ] using
        ((hcCont.mono hsub).pow 2) :
          ContinuousOn (fun r => c r ^ 2) (uIcc δ ρ)).intervalIntegrable
  have hbCont : ContinuousOn b (Icc δ R) :=
    finiteBallSphereRadialMean_continuousOn_positive_annulus
      (m + 3) R δ hδ (lt_of_le_of_lt hδρ hρR) z hz k hTraceLim
  have hBInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ :=
    (by
      simpa only [uIcc_of_le hδρ] using
        ((hbCont.mono hsub).pow 2) :
          ContinuousOn (fun r => b r ^ 2) (uIcc δ ρ)).intervalIntegrable
  have hTraceInt : IntervalIntegrable
      (fun r => ‖v r - v R‖ ^ 2) volume δ ρ :=
    (by
      simpa only [uIcc_of_le hδρ] using
        (((hvCont.mono hsub).sub continuousOn_const).norm.pow 2) :
          ContinuousOn (fun r => ‖v r - v R‖ ^ 2)
            (uIcc δ ρ)).intervalIntegrable
  have hTraceZeroCont : ContinuousOn
      (fun r => v r - c r • e) (Icc δ R) :=
    hvCont.sub (hcCont.smul continuousOn_const)
  have hTraceZeroInt : IntervalIntegrable
      (fun r => ‖(v R - c R • e) - (v r - c r • e)‖ ^ 2)
      volume δ ρ := by
    have hCont : ContinuousOn
        (fun r => ‖(v R - c R • e) - (v r - c r • e)‖ ^ 2)
        (uIcc δ ρ) := by
      simpa only [uIcc_of_le hδρ] using
        ((continuousOn_const.sub (hTraceZeroCont.mono hsub)).norm.pow 2)
    exact hCont.intervalIntegrable
  have hTraceDeriv : ∀ r ∈ Ioo δ R,
      HasDerivAt (fun s => v s - c s • e)
        (dv r k - dc r • e) r := by
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) R := ⟨hδ.trans hr.1, hr.2⟩
    have hvr := finiteBallSphereFamily_hasDerivAt_interior
      (m + 3) R z hz r hr' k
    have hcr := sphereMeanCoefficient_hasDerivAt
      (m + 3) v r (dv r k) hvr
    exact hvr.sub (hcr.smul_const e)
  have hb : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt b (deriv b r) r := by
    intro r hr
    exact ((finiteBallSphereRadialMean_hasDerivAt_interior
      (m + 3) R z hz k r hr).differentiableAt).hasDerivAt
  have hcPic : ∀ r ∈ Ioo (0 : ℝ) R, c r = b r / r := by
    intro r hr
    exact scalarSphereRadialMean_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k) r hr.1
  have hdcPic : ∀ r ∈ Ioo (0 : ℝ) R,
      dc r = deriv (fun s => b s / s) r := by
    intro r hr
    exact scalarSphereRadialMean_deriv_div (m + 3)
      (fun s y => (g s y) k) (fun s => hg s k)
      (dv r k) r hr.1
      (finiteBallSphereFamily_hasDerivAt_interior
        (m + 3) R z hz r hr k)
  have hPicFluxReg (ε : ℝ) (hε : 0 < ε) (hεR : ε ≤ R) :
      ContinuousOn (profilePiconeBoundaryFlux m p.f p.F b)
        (uIcc ε R) ∧
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m p.f p.F b))
        volume ε R := by
    simpa only [b, g, hg] using
      (actual_finiteBallSphere_profilePiconeFlux_annulus_regular
        m R p.hR p.f p.F p.Hf u p.hfC2 p.hFC2 p.hHf hu.1
        (fun r hr => p.hFposAll r hr.1) p.hfpos
        (p.profile_order m R) p.hfFactor hu.2 k ε hε hεR)
  have hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    simpa only [b, g, hg] using
      (actual_finiteBallSphereRadialMean_right_limit
        (m + 3) R p.hR p.f p.Hf u
        p.hHf.continuous.continuousAt hHf0 hu.1.continuous.continuousAt
        p.hfFactor hfpos hz k)
  have hFluxCont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (bridgeOriginFlux m p.f p.F b) (uIcc ε R) := by
    intro ε hε hεR
    simpa only [b, g, hg] using
      (actual_finiteBallSphere_bridgeOriginFlux_continuousOn
        m R p.hR p.f p.F u hfC1 hFDiff hfpos
        hu.1.contDiffOn hu.2 k ε hε hεR)
  have hFluxLim : Tendsto (bridgeOriginFlux m p.f p.F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [b, g, hg] using
      (actual_finiteBallSphereRadialMean_flux_right_limit
        m R p.hR p.f p.F p.Hf u p.α p.β
        p.Af p.Bf p.AF p.BF p.hfTaylor p.hFTaylor
        p.hHf.continuous.continuousAt hHf0
        hu.1.continuous.continuousAt p.hfFactor hfpos hz k)
  have hresult := p.annular_trace_l2_controlled_by_bridge
    m R e v (fun r => dv r k) angular c dc b (deriv b) δ ρ
    hδ hδρ hρR he hcR hv hdv hgap hfullInt hmeanInt
    hdvCont hdcCont hCInt hBInt hTraceInt hTraceZeroInt
    hTraceZeroCont hTraceDeriv hb hbR hcPic hdcPic hDint
    (fun ε hε hεR => (hPicFluxReg ε hε hεR).1)
    (fun ε hε hεR => (hPicFluxReg ε hε hεR).2)
    hblim hFluxCont hFluxLim hFluxInt
  simpa only [scalarSphereBridgeDensity] using hresult

end

end BrezisOP6
