import BrezisOP6.WeakBallRestriction
import BrezisOP6.RadialWeakBaseBridge
import BrezisOP6.WeakStrongClosureMain

/-!
# Fixed-trace `H¹∩L⁴` density for the physical ball

The weak trace is the global weak gradient of the zero-extended
difference from the canonical smooth radial base.  Inward dilation,
joint mollification, and diagonal selection produce one sequence of
interior smooth vector perturbations.  This module inserts that sequence
into the actual weak-energy certificate and proves the exact strong
convergence required by the finite-ball closure theorem.
-/

namespace BrezisOP6

open MeasureTheory Filter Metric
open scoped Topology ENNReal

noncomputable section

theorem physical_weak_fixed_trace_strong_closure
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (U : WeakFixedTraceCompetitor
      (WeakH1L4BallField.ofGlobalC1 (m + 3) R
        (radialRegularField (m + 3) p.Hf)
        (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf))) :
    WeakSmoothFixedTraceStrongClosure m R p.f U.field := by
  let n := m + 3
  haveI : NeZero n := ⟨by dsimp [n]; omega⟩
  let b : GLEuclidean n → GLEuclidean n := radialRegularField n p.Hf
  have hb : ContDiff ℝ 1 b := radialRegularField_contDiff_one n p.Hf p.hHf
  let base : WeakH1L4BallField n R :=
    WeakH1L4BallField.ofGlobalC1 n R b hb
  obtain ⟨q, hqC1, hqZero, hqValue, hqGradient⟩ :=
    U.exists_ball_strong_approx_of_zeroTrace p.hR base
  let v (k : ℕ) : GLEuclidean n → GLEuclidean n :=
    fun x => b x + q k x
  have hvC1 (k : ℕ) : ContDiff ℝ 1 (v k) :=
    hb.add (hqC1 k)
  let V (k : ℕ) : WeakH1L4BallField n R :=
    WeakH1L4BallField.ofGlobalC1 n R (v k) (hvC1 k)
  have hSmooth (k : ℕ) : SmoothBallCompetitor m R p.f (V k).u ∧
      (V k).grad = fderiv ℝ (V k).u := by
    constructor
    · change SmoothBallCompetitor m R p.f
        (fun x => radialRegularField n p.Hf x + q k x)
      exact smoothBallCompetitor_regular_add m R p.f p.Hf
        p.hHf p.hfFactor (q k) (hqC1 k) (hqZero k)
    · rfl
  let w := zeroExtendedDifference n R U.field.u base.u
  let G := zeroExtendedGradientDifference n R U.field.grad base.grad
  have hBaseU : base.u = b := rfl
  have hBaseGrad : base.grad = fderiv ℝ b := rfl
  have hValueEq (k : ℕ) :
      (fun x => (V k).u x - U.field.u x) =ᵐ[weakBallMeasure n R]
        (fun x => q k x - w x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    change (b x + q k x) - U.field.u x = q k x - w x
    have hw : w x = U.field.u x - b x := by
      simp [w, zeroExtendedDifference, hx, hBaseU]
    rw [hw]
    abel
  have hValueNorm (k : ℕ) :
      lpNorm (fun x => (V k).u x - U.field.u x) 4
        (weakBallMeasure n R) =
      lpNorm (fun x => q k x - w x) 4
        (weakBallMeasure n R) := by
    have hMeas : AEStronglyMeasurable
        (fun x => (V k).u x - U.field.u x)
        (weakBallMeasure n R) := (V k).uMeas.sub U.field.uMeas
    have hMeas' := hMeas.congr (hValueEq k)
    rw [← toReal_eLpNorm hMeas, ← toReal_eLpNorm hMeas',
      eLpNorm_congr_ae (hValueEq k)]
  have hValueLim : Tendsto
      (fun k => lpNorm (fun x => (V k).u x - U.field.u x) 4
        (weakBallMeasure n R)) atTop (nhds 0) := by
    simp only [hValueNorm]
    exact hqValue
  have hGradientEq (k : ℕ) (i : Fin n) :
      (fun x => (V k).grad x (EuclideanSpace.single i (1 : ℝ)) -
        U.field.grad x (EuclideanSpace.single i (1 : ℝ)))
        =ᵐ[weakBallMeasure n R]
      (fun x => (fderiv ℝ (q k) x)
        (EuclideanSpace.single i (1 : ℝ)) -
          G x (EuclideanSpace.single i (1 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    let ei : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
    have hd : fderiv ℝ (v k) x =
        fderiv ℝ b x + fderiv ℝ (q k) x :=
      fderiv_fun_add (hb.differentiable_one x)
        ((hqC1 k).differentiable_one x)
    have hGx : G x = U.field.grad x - fderiv ℝ b x := by
      simp [G, zeroExtendedGradientDifference, hx, hBaseGrad]
    change (fderiv ℝ (v k) x) ei - U.field.grad x ei =
      (fderiv ℝ (q k) x) ei - G x ei
    rw [hd, hGx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    abel
  have hGradientNorm (k : ℕ) (i : Fin n) :
      lpNorm (fun x => (V k).grad x
        (EuclideanSpace.single i (1 : ℝ)) -
          U.field.grad x (EuclideanSpace.single i (1 : ℝ)))
        2 (weakBallMeasure n R) =
      lpNorm (fun x => (fderiv ℝ (q k) x)
        (EuclideanSpace.single i (1 : ℝ)) -
          G x (EuclideanSpace.single i (1 : ℝ)))
        2 (weakBallMeasure n R) := by
    let ei : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
    let ev : (GLEuclidean n →L[ℝ] GLEuclidean n) →L[ℝ]
        GLEuclidean n := ContinuousLinearMap.apply ℝ (GLEuclidean n) ei
    have hMeas : AEStronglyMeasurable
        (fun x => (V k).grad x ei - U.field.grad x ei)
        (weakBallMeasure n R) :=
      (ev.continuous.aestronglyMeasurable.comp_aemeasurable
        (V k).gradMeas.aemeasurable).sub
      (ev.continuous.aestronglyMeasurable.comp_aemeasurable
        U.field.gradMeas.aemeasurable)
    have hMeas' := hMeas.congr (hGradientEq k i)
    rw [← toReal_eLpNorm hMeas, ← toReal_eLpNorm hMeas',
      eLpNorm_congr_ae (hGradientEq k i)]
  refine ⟨V, hSmooth, ?_, ?_⟩
  · exact hValueLim
  · intro i
    convert hqGradient i using 1
    funext k
    exact hGradientNorm k i

end

end BrezisOP6
