import BrezisOP6.SphereFiniteFamily
import BrezisOP6.EnergyQuotientPuncturedC1

/-!
# The actual outer spherical `L²` trace

Continuity of the quotient on a positive-radius closed annulus makes its
spherical trace continuous in the compact-open topology and hence in
`L²`.  At the outer endpoint the finite-ball family records the identity
boundary value, so the interior traces converge to that value from the
left.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

private def positiveClosedRayCoordinate
    (n : ℕ) (R a : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContinuousOn z (energyPositiveClosedBall n R))
    (ha : 0 < a) (k : Fin n) (r : ℝ) :
    C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) := by
  by_cases hr : r ∈ Icc a R
  · have hRay : Continuous
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          r • (ω : GLEuclidean n)) :=
      (continuous_const_smul r).comp continuous_subtype_val
    have hMaps : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
        r • (ω : GLEuclidean n) ∈ energyPositiveClosedBall n R := by
      intro ω
      have hrpos : 0 < r := lt_of_lt_of_le ha hr.1
      change 0 < ‖r • (ω : GLEuclidean n)‖ ∧
        ‖r • (ω : GLEuclidean n)‖ ≤ R
      rw [show r • (ω : GLEuclidean n) =
          energySphereRay n ω r from rfl,
        energySphereRay_norm n ω r hrpos.le]
      exact ⟨hrpos, hr.2⟩
    exact ⟨fun ω => (z (r • (ω : GLEuclidean n))) k,
      (EuclideanSpace.proj k).continuous.comp
        (hz.comp_continuous hRay hMaps)⟩
  · exact 0

private theorem positiveClosedRayCoordinate_continuousOn
    (n : ℕ) (R a : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContinuousOn z (energyPositiveClosedBall n R))
    (ha : 0 < a) (k : Fin n) :
    ContinuousOn (positiveClosedRayCoordinate n R a z hz ha k)
      (Icc a R) := by
  let S := Metric.sphere (0 : GLEuclidean n) 1
  let U : Set (ℝ × S) := Icc a R ×ˢ univ
  have hRay : Continuous (fun p : ℝ × S =>
      p.1 • (p.2 : GLEuclidean n)) :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  have hMaps : MapsTo
      (fun p : ℝ × S => p.1 • (p.2 : GLEuclidean n))
      U (energyPositiveClosedBall n R) := by
    intro p hp
    have hrpos : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
    change 0 < ‖p.1 • (p.2 : GLEuclidean n)‖ ∧
      ‖p.1 • (p.2 : GLEuclidean n)‖ ≤ R
    rw [show p.1 • (p.2 : GLEuclidean n) =
        energySphereRay n p.2 p.1 from rfl,
      energySphereRay_norm n p.2 p.1 hrpos.le]
    exact ⟨hrpos, hp.1.2⟩
  have hZ : ContinuousOn
      (fun p : ℝ × S => z (p.1 • (p.2 : GLEuclidean n))) U :=
    hz.comp hRay.continuousOn hMaps
  have hCoord : ContinuousOn
      (fun p : ℝ × S => (z (p.1 • (p.2 : GLEuclidean n))) k) U :=
    (EuclideanSpace.proj k).continuous.comp_continuousOn hZ
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  apply hCoord.congr
  intro p hp
  change (positiveClosedRayCoordinate n R a z hz ha k p.1) p.2 = _
  simp [positiveClosedRayCoordinate, hp.1]

theorem finiteBallSphereFamily_trace_tendsto_outer_left
    (n : ℕ) (R a : ℝ) (hR : 0 < R)
    (ha : 0 < a) (haR : a < R)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hzClosed : ContinuousOn z (energyPositiveClosedBall n R))
    (hboundary : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      z (energySphereRay n ω R) = (ω : GLEuclidean n))
    (k : Fin n) :
    Tendsto
      (fun r => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r)
      (𝓝[<] R)
      (𝓝 (scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) R)) := by
  let C : ℝ → C(Metric.sphere (0 : GLEuclidean n) 1, ℝ) :=
    positiveClosedRayCoordinate n R a z hzClosed ha k
  let L : ℝ → UnitSphereL2 n :=
    fun r => (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ) (C r)
  have hCont : ContinuousOn L (Icc a R) :=
    (ContinuousMap.toLp 2 (unitSphereMeasure n) ℝ).continuous.comp_continuousOn
      (positiveClosedRayCoordinate_continuousOn n R a z hzClosed ha k)
  have hRmem : R ∈ Icc a R := ⟨haR.le, le_rfl⟩
  have hL : Tendsto L (𝓝[<] R) (𝓝 (L R)) :=
    (hCont R hRmem).mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT haR))
  have hEq (r : ℝ) (hr : r ∈ Icc a R) :
      L r = scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r := by
    have hpoint (ω : Metric.sphere (0 : GLEuclidean n) 1) :
        (C r) ω = (finiteBallSphereFamily n R z r ω) k := by
      have hC : (C r) ω = (z (r • (ω : GLEuclidean n))) k := by
        simp [C, positiveClosedRayCoordinate, hr]
      rw [hC]
      by_cases hrR : r = R
      · subst r
        rw [show R • (ω : GLEuclidean n) =
            energySphereRay n ω R from rfl, hboundary ω,
          finiteBallSphereFamily_outer]
      · have hrpos : 0 < r := lt_of_lt_of_le ha hr.1
        have hrlt : r < R := lt_of_le_of_ne hr.2 hrR
        rw [finiteBallSphereFamily_interior n R z r ⟨hrpos, hrlt⟩]
    apply Lp.ext
    have hc := ContinuousMap.coeFn_toLp
      (p := 2) (μ := unitSphereMeasure n) (𝕜 := ℝ) (C r)
    have hf := (finiteBallSphereFamily_memLp n R z hz r k).coeFn_toLp
    filter_upwards [hc, hf] with ω hcw hfw
    calc
      L r ω = (C r) ω := hcw
      _ = (finiteBallSphereFamily n R z r ω) k := hpoint ω
      _ = (scalarSphereFamilyTrace n
          (fun s y => (finiteBallSphereFamily n R z s y) k)
          (fun s => finiteBallSphereFamily_memLp n R z hz s k) r) ω := hfw.symm
  have hEventual :
      (fun r => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r)
      =ᶠ[𝓝[<] R] L := by
    filter_upwards [Icc_mem_nhdsLT haR] with r hr
    exact (hEq r hr).symm
  rw [← hEq R hRmem] at ⊢
  exact hL.congr' hEventual.symm

/-- For a smooth finite-ball competitor with vortex boundary values, the
actual quotient traces tend in `L²` to the identity sphere trace from
inside the ball. -/
theorem actual_quotient_finiteBallSphereFamily_trace_tendsto_outer_left
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hfC1 : ContDiff ℝ 1 f)
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean n) R))
    (huBoundary : ∀ x : GLEuclidean n, ‖x‖ = R →
      u x = radialVortex n f x)
    (k : Fin n) :
    let z : GLEuclidean n → GLEuclidean n :=
      fun x => (f ‖x‖)⁻¹ • u x
    let hz : ContDiffOn ℝ 1 z
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
        radialQuotient_contDiffOn_puncturedBall n R f u
          hfC1 hfpos huC1
    Tendsto
      (fun r => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r)
      (𝓝[<] R)
      (𝓝 (scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) R)) := by
  dsimp only
  let z : GLEuclidean n → GLEuclidean n :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall n R f u
      hfC1 hfpos huC1
  have hsub : energyPositiveClosedBall n R ⊆
      Metric.closedBall (0 : GLEuclidean n) R := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
  have huOn : ContinuousOn u (energyPositiveClosedBall n R) :=
    huC1.continuousOn.mono hsub
  have hfOn : ContinuousOn
      (fun x : GLEuclidean n => f ‖x‖)
      (energyPositiveClosedBall n R) :=
    (hfC1.continuous.comp continuous_norm).continuousOn
  have hzClosed : ContinuousOn z
      (energyPositiveClosedBall n R) := by
    exact (hfOn.inv₀ (fun x hx =>
      ne_of_gt (hfpos ‖x‖ hx.1 hx.2))).smul huOn
  have hBoundary (ω : Metric.sphere (0 : GLEuclidean n) 1) :
      z (energySphereRay n ω R) = (ω : GLEuclidean n) := by
    let x := energySphereRay n ω R
    have hxNorm : ‖x‖ = R := energySphereRay_norm n ω R hR.le
    have hradial : radialVortex n f x =
        f R • (ω : GLEuclidean n) := by
      calc
        radialVortex n f x = (f R / R) • x := by
          simp [radialVortex, hxNorm]
        _ = ((f R / R) * R) • (ω : GLEuclidean n) := by
          simp only [x, energySphereRay, smul_smul]
        _ = f R • (ω : GLEuclidean n) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hR)]
    change (f ‖x‖)⁻¹ • u x = (ω : GLEuclidean n)
    rw [huBoundary x hxNorm, hradial, hxNorm, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (hfpos R hR le_rfl)), one_smul]
  have hhalf : 0 < R / 2 := by positivity
  have hhalfR : R / 2 < R := by linarith
  exact finiteBallSphereFamily_trace_tendsto_outer_left
    n R (R / 2) hR hhalf hhalfR z hz hzClosed hBoundary k

end

end BrezisOP6
