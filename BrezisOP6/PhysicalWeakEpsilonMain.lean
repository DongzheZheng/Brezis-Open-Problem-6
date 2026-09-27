import BrezisOP6.PhysicalWeakBallMain
import BrezisOP6.WeakEpsilonMainTransfer

/-!
# The arbitrary-parameter unit-ball theorem

The canonical unit-ball base is the inverse dilation of the regular
large-ball radial representative.  Its forward dilation is exactly the
canonical large-ball weak field, including the certified gradient.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

private theorem weakBallField_ext_of_u_grad
    {n : ℕ} {R : ℝ} (A B : WeakH1L4BallField n R)
    (hu : A.u = B.u) (hg : A.grad = B.grad) : A = B := by
  cases A with
  | mk u grad uMeas gradMeas uL2 uL4 gradL2 weakDerivative =>
    cases B with
    | mk u' grad' uMeas' gradMeas' uL2' uL4' gradL2' weakDerivative' =>
      dsimp at hu hg
      cases hu
      cases hg
      rfl

/-- The regular radial representative at the paper's coherence length
`ε`, obtained by pulling the radius-`1/ε` profile back to the unit ball. -/
def physicalWeakUnitBase (m : ℕ) (ε : ℝ)
    (p : PhysicalRadialData m (1 / ε)) :
    WeakH1L4BallField (m + 3) 1 :=
  WeakH1L4BallField.ofGlobalC1 (m + 3) 1
    (fun x => radialRegularField (m + 3) p.Hf (ε⁻¹ • x))
    ((radialRegularField_contDiff_one (m + 3) p.Hf p.hHf).comp
      (contDiff_const_smul ε⁻¹))

/-- The profile representative commutes exactly with dilation at the
level of both the field and its weak-gradient certificate. -/
theorem physicalWeakUnitBase_dilate_eq_largeBase
    (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (p : PhysicalRadialData m (1 / ε)) :
    (physicalWeakUnitBase m ε p).dilate ε hε =
      WeakH1L4BallField.ofGlobalC1 (m + 3) (1 / ε)
        (radialRegularField (m + 3) p.Hf)
        (radialRegularField_contDiff_one (m + 3) p.Hf p.hHf) := by
  let b : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    radialRegularField (m + 3) p.Hf
  have hu : ((physicalWeakUnitBase m ε p).dilate ε hε).u = b := by
    funext x
    change b (ε⁻¹ • (ε • x)) = b x
    simp [smul_smul, hε.ne']
  have hg : ((physicalWeakUnitBase m ε p).dilate ε hε).grad =
      fderiv ℝ b := by
    funext x
    change ε • (fderiv ℝ (fun y => b (ε⁻¹ • y)) (ε • x)) =
      fderiv ℝ b x
    rw [fderiv_comp_smul]
    simp [smul_smul, hε.ne']
  exact weakBallField_ext_of_u_grad _ _ hu hg

/-- On the unit ball the certified smooth representative is exactly the
radial vortex with the paper's rescaled profile
`f_ε(r) = f_(1/ε)(r/ε)`. -/
theorem physicalWeakUnitBase_eq_vortex_on_unitBall
    (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (p : PhysicalRadialData m (1 / ε))
    (x : GLEuclidean (m + 3))
    (hx : x ∈ Metric.ball (0 : GLEuclidean (m + 3)) 1) :
    (physicalWeakUnitBase m ε p).u x =
      radialVortex (m + 3) (fun r => p.f (r / ε)) x := by
  have hy : ε⁻¹ • x ∈
      Metric.ball (0 : GLEuclidean (m + 3)) (1 / ε) := by
    apply (ball_dilate_membership (m + 3) 1 ε hε (ε⁻¹ • x)).1
    simpa [smul_smul, hε.ne'] using hx
  have hbase := radialRegularField_eq_vortex_on_ball
    (m + 3) (1 / ε) p.f p.Hf p.hfFactor (ε⁻¹ • x) hy
  have hscale := radialVortex_dilate (m + 3) ε⁻¹
    (inv_pos.mpr hε) p.f x
  change radialRegularField (m + 3) p.Hf (ε⁻¹ • x) = _
  rw [hbase, hscale]
  congr 1
  funext r
  simp only [inv_mul_eq_div]

theorem physicalWeakUnitBase_ae_eq_vortex
    (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (p : PhysicalRadialData m (1 / ε)) :
    (physicalWeakUnitBase m ε p).u =ᵐ[weakBallMeasure (m + 3) 1]
      radialVortex (m + 3) (fun r => p.f (r / ε)) := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact physicalWeakUnitBase_eq_vortex_on_unitBall m ε hε p x hx

/-- The full `n=m+3` weak fixed-trace theorem on the unit ball for every
positive coherence length.  Its only mathematical inputs beyond the
certified competitor are the physical radial profile data, the published
whole-space vortex minimum, and the sharp spherical Poincaré inequality. -/
theorem physical_weak_unit_epsilon_minimum_and_ae_equality
    (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (p : PhysicalRadialData m (1 / ε))
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor (physicalWeakUnitBase m ε p)) :
    weakBallEnergyEpsilon (m + 3) 1 ε
        (physicalWeakUnitBase m ε p).u
        (physicalWeakUnitBase m ε p).grad ≤
      weakBallEnergyEpsilon (m + 3) 1 ε U.field.u U.field.grad ∧
    (weakBallEnergyEpsilon (m + 3) 1 ε U.field.u U.field.grad =
      weakBallEnergyEpsilon (m + 3) 1 ε
        (physicalWeakUnitBase m ε p).u
        (physicalWeakUnitBase m ε p).grad →
      U.field.u =ᵐ[weakBallMeasure (m + 3) 1]
        (physicalWeakUnitBase m ε p).u) := by
  apply weak_unit_epsilon_minimum_and_ae_equality_of_large_ball
    (m + 3) (by omega) ε hε (physicalWeakUnitBase m ε p)
    ?_ U
  rw [physicalWeakUnitBase_dilate_eq_largeBase m ε hε p]
  intro V
  exact physical_weak_ball_minimum_and_ae_equality
    m (1 / ε) p hPublished hLocal V

end

end BrezisOP6
