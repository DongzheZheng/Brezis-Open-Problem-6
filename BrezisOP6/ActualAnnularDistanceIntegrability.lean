import BrezisOP6.AnnularDistanceWeightBound

/-!
# Compact-annulus integrability of the physical distance

Away from the origin the radial vortex and every smooth competitor are
continuous.  Their squared distance is therefore integrable on each
compact annulus.  This discharges the spatial integrability input of the
polar distance formula without invoking global quotient regularity.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem actual_annular_distance_integrable_of_continuous
    (n : ℕ) (δ ρ : ℝ) (hδ : 0 < δ)
    (f : ℝ → ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hf : Continuous f) (hu : Continuous u) :
    IntegrableOn
      (fun x : GLEuclidean n =>
        ‖u x - radialVortex n f x‖ ^ 2)
      (energyPositiveAnnulus n δ ρ) volume := by
  let K : Set (GLEuclidean n) :=
    {x | ‖x‖ ∈ Icc δ ρ}
  have hKclosed : IsClosed K := by
    exact isClosed_Icc.preimage continuous_norm
  have hKsub : K ⊆ Metric.closedBall (0 : GLEuclidean n) ρ := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : GLEuclidean n) ρ).of_isClosed_subset
      hKclosed hKsub
  have hKpos (x : GLEuclidean n) (hx : x ∈ K) :
      ‖x‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hx.1)
  have hV : ContinuousOn (radialVortex n f) K := by
    have hF : Continuous (fun x : GLEuclidean n => f ‖x‖) :=
      hf.comp continuous_norm
    have hQuot : ContinuousOn
        (fun x : GLEuclidean n => f ‖x‖ / ‖x‖) K :=
      hF.continuousOn.div continuous_norm.continuousOn hKpos
    simpa only [radialVortex] using hQuot.smul continuous_id.continuousOn
  have hDist : ContinuousOn
      (fun x : GLEuclidean n =>
        ‖u x - radialVortex n f x‖ ^ 2) K :=
    ((hu.continuousOn.sub hV).norm.pow 2)
  have hAnnSub : energyPositiveAnnulus n δ ρ ⊆ K := by
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  exact (hDist.integrableOn_compact hKcompact).mono_set hAnnSub

/-- Smoothness of the quotient away from the origin gives the scalar
trace-distance integrability needed by the physical annulus estimate. -/
theorem finiteBallSphereFamily_trace_distance_intervalIntegrable
    (n : ℕ) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n) :
    IntervalIntegrable (fun r =>
      ‖scalarSphereFamilyTrace n
          (fun s y => (finiteBallSphereFamily n R z s y) k)
          (fun s => finiteBallSphereFamily_memLp n R z hz s k) r -
        scalarSphereFamilyTrace n
          (fun s y => (finiteBallSphereFamily n R z s y) k)
          (fun s => finiteBallSphereFamily_memLp n R z hz s k) R‖ ^ 2)
      volume δ ρ := by
  let v : ℝ → UnitSphereL2 n := fun r =>
    scalarSphereFamilyTrace n
      (fun s y => (finiteBallSphereFamily n R z s y) k)
      (fun s => finiteBallSphereFamily_memLp n R z hz s k) r
  have hvCont : ContinuousOn v (Icc δ ρ) := by
    apply continuousOn_of_forall_continuousAt
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hδ hr.1
    have hrR : r < R := lt_of_le_of_lt hr.2 hρR
    exact (finiteBallSphereFamily_hasDerivAt_interior n R z hz
      r ⟨hrpos, hrR⟩ k).continuousAt
  have hDCont : ContinuousOn (fun r => ‖v r - v R‖ ^ 2)
      (Icc δ ρ) := (hvCont.sub continuousOn_const).norm.pow 2
  exact hDCont.intervalIntegrable_of_Icc hδρ

/-- The final polar transfer estimate has no integrability premise:
continuity of the physical field and regularity of its quotient supply
both integrable representatives automatically. -/
theorem actual_annular_distance_le_trace_of_smooth
    (n : ℕ) (hn : 1 ≤ n) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (f : ℝ → ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hfCont : Continuous f) (huCont : Continuous u)
    (hfpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < f r)
    (hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1)
    (hz : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (f ‖x‖)⁻¹ • u x)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R}) :
    (∫ x in energyPositiveAnnulus n δ ρ,
        ‖u x - radialVortex n f x‖ ^ 2) ≤
      R ^ (n - 1) *
        (∑ k : Fin n,
          ∫ r in δ..ρ,
            ‖scalarSphereFamilyTrace n
                (fun s y => (finiteBallSphereFamily n R
                  (fun x => (f ‖x‖)⁻¹ • u x) s y) k)
                (fun s => finiteBallSphereFamily_memLp n R
                  (fun x => (f ‖x‖)⁻¹ • u x) hz s k) r -
              scalarSphereFamilyTrace n
                (fun s y => (finiteBallSphereFamily n R
                  (fun x => (f ‖x‖)⁻¹ • u x) s y) k)
                (fun s => finiteBallSphereFamily_memLp n R
                  (fun x => (f ‖x‖)⁻¹ • u x) hz s k) R‖ ^ 2) := by
  exact actual_annular_distance_le_finite_trace_integrals
    n hn δ ρ R hδ hδρ hρR f u hfCont hfpos hflt hz
    (actual_annular_distance_integrable_of_continuous
      n δ ρ hδ f u hfCont huCont)
    (fun k => finiteBallSphereFamily_trace_distance_intervalIntegrable
      n δ ρ R hδ hδρ hρR
      (fun x => (f ‖x‖)⁻¹ • u x) hz k)

end

end BrezisOP6
