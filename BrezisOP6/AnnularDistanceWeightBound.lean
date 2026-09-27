import BrezisOP6.ActualAnnularDistance

/-!
# Removing the bounded radial weight on a compact annulus

The physical squared distance has weight `r^(n-1) f(r)^2` after polar
integration.  This elementary estimate removes any continuous upper
bound on that weight, leaving the unweighted trace distances controlled
by the radial bridge.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

theorem annular_weighted_finite_trace_bound
    (n : ℕ) (δ ρ R C : ℝ)
    (hδρ : δ ≤ ρ)
    (w : ℝ → ℝ) (v : Fin n → ℝ → UnitSphereL2 n)
    (hwCont : ContinuousOn w (Icc δ ρ))
    (hwLe : ∀ r ∈ Icc δ ρ, w r ≤ C)
    (hTraceInt : ∀ k : Fin n,
      IntervalIntegrable (fun r => ‖v k r - v k R‖ ^ 2)
        volume δ ρ) :
    (∫ r in δ..ρ,
        w r * (∑ k : Fin n, ‖v k r - v k R‖ ^ 2)) ≤
      C * (∑ k : Fin n,
        ∫ r in δ..ρ, ‖v k r - v k R‖ ^ 2) := by
  let A : ℝ → ℝ :=
    fun r => ∑ k : Fin n, ‖v k r - v k R‖ ^ 2
  have hAInt : IntervalIntegrable A volume δ ρ := by
    simpa only [A, Finset.sum_fn] using
      (IntervalIntegrable.sum Finset.univ (fun k _ => hTraceInt k))
  have hwInt : IntervalIntegrable (fun r => w r * A r)
      volume δ ρ := by
    apply hAInt.continuousOn_mul
    simpa only [uIcc_of_le hδρ] using hwCont
  have hPoint (r : ℝ) (hr : r ∈ Icc δ ρ) :
      w r * A r ≤ C * A r := by
    have hA : 0 ≤ A r :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hwLe r hr) hA
  have hBound := intervalIntegral.integral_mono_on hδρ
    hwInt (hAInt.const_mul C) hPoint
  rw [intervalIntegral.integral_const_mul] at hBound
  have hSum : (∫ r in δ..ρ, A r) =
      ∑ k : Fin n, ∫ r in δ..ρ, ‖v k r - v k R‖ ^ 2 := by
    exact intervalIntegral.integral_finset_sum
      (s := Finset.univ)
      (f := fun k r => ‖v k r - v k R‖ ^ 2)
      (fun k _ => hTraceInt k)
  simpa only [A, hSum] using hBound

/-- A positive radial profile strictly below one makes the polar weight
no larger than the outer radius's Jacobian on every interior annulus. -/
theorem radial_profile_polar_weight_le_radius_pow
    (n : ℕ) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hρR : ρ < R)
    (f : ℝ → ℝ)
    (hfpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < f r)
    (hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1)
    (r : ℝ) (hr : r ∈ Icc δ ρ) :
    r ^ (n - 1) * f r ^ 2 ≤ R ^ (n - 1) := by
  have hrpos : 0 < r := lt_of_lt_of_le hδ hr.1
  have hrR : r < R := lt_of_le_of_lt hr.2 hρR
  have hpow : r ^ (n - 1) ≤ R ^ (n - 1) :=
    pow_le_pow_left₀ hrpos.le hrR.le _
  have hf2 : f r ^ 2 ≤ (1 : ℝ) := by
    have h := pow_le_pow_left₀ (hfpos r ⟨hrpos, hrR⟩).le
      (hflt r ⟨hrpos, hrR⟩).le 2
    simpa using h
  calc
    r ^ (n - 1) * f r ^ 2 ≤ r ^ (n - 1) * 1 :=
      mul_le_mul_of_nonneg_left hf2 (pow_nonneg hrpos.le _)
    _ = r ^ (n - 1) := by ring
    _ ≤ R ^ (n - 1) := hpow

theorem radial_profile_polar_weight_continuousOn
    (n : ℕ) (δ ρ : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    ContinuousOn (fun r => r ^ (n - 1) * f r ^ 2) (Icc δ ρ) := by
  exact ((continuous_id.pow (n - 1)).mul (hf.pow 2)).continuousOn

/-- The physical annular `L²` distance is bounded by the unweighted sum
of coordinate trace distances for a smooth competitor. -/
theorem actual_annular_distance_le_finite_trace_integrals
    (n : ℕ) (hn : 1 ≤ n) (δ ρ R : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (f : ℝ → ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hfCont : Continuous f)
    (hfpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < f r)
    (hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1)
    (hz : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (f ‖x‖)⁻¹ • u x)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hAnnInt : IntegrableOn
      (fun x : GLEuclidean n =>
        ‖u x - radialVortex n f x‖ ^ 2)
      (energyPositiveAnnulus n δ ρ) volume)
    (hTraceInt : ∀ k : Fin n,
      IntervalIntegrable (fun r =>
        ‖scalarSphereFamilyTrace n
            (fun s y => (finiteBallSphereFamily n R
              (fun x => (f ‖x‖)⁻¹ • u x) s y) k)
            (fun s => finiteBallSphereFamily_memLp n R
              (fun x => (f ‖x‖)⁻¹ • u x) hz s k) r -
          scalarSphereFamilyTrace n
            (fun s y => (finiteBallSphereFamily n R
              (fun x => (f ‖x‖)⁻¹ • u x) s y) k)
            (fun s => finiteBallSphereFamily_memLp n R
              (fun x => (f ‖x‖)⁻¹ • u x) hz s k) R‖ ^ 2)
        volume δ ρ) :
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
  let z : GLEuclidean n → GLEuclidean n :=
    fun x => (f ‖x‖)⁻¹ • u x
  let v : Fin n → ℝ → UnitSphereL2 n :=
    fun k r => scalarSphereFamilyTrace n
      (fun s y => (finiteBallSphereFamily n R z s y) k)
      (fun s => finiteBallSphereFamily_memLp n R z hz s k) r
  have hEq := actual_annular_distance_eq_weighted_trace
    n hn δ ρ R hδ hδρ hρR f u
    (fun r hr => ne_of_gt (hfpos r hr)) hz hAnnInt
  have hWeight := annular_weighted_finite_trace_bound
    n δ ρ R (R ^ (n - 1)) hδρ
    (fun r => r ^ (n - 1) * f r ^ 2) v
    (radial_profile_polar_weight_continuousOn n δ ρ f hfCont)
    (radial_profile_polar_weight_le_radius_pow n δ ρ R
      hδ hρR f hfpos hflt)
    hTraceInt
  simpa only [z, v, mul_assoc] using hEq.le.trans hWeight

end

end BrezisOP6
