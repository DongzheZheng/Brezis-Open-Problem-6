import BrezisOP6.SphereFiniteFamily
import BrezisOP6.SphereLocalPoincare

/-!
# Sharp angular gap for the explicit finite-ball family

Inside the ball the gap follows from the sphere-local Poincaré input and
punctured `C¹` regularity.  At radius zero the chosen family is the zero
field; at the outer radius it is the identity field.  Both endpoint
restrictions are globally smooth, so the same local spectral input applies
without any extension of the singular quotient.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

theorem finiteBallSphereFamily_angular_gap
    (m : ℕ) (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin (m + 3)) :
    ∀ r ∈ Icc (0 : ℝ) R,
      (m + 2 : ℝ) *
        ‖sphereMeanZeroPart (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
            (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
            r)‖ ^ 2 ≤
      unitSphereAngularEnergy (m + 3)
        (fun y => (finiteBallSphereFamily (m + 3) R z r y) k) := by
  intro r hr
  let g : ℝ → GLEuclidean (m + 3) → ℝ :=
    fun s y => (finiteBallSphereFamily (m + 3) R z s y) k
  let hg : ∀ s, MemLp
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 => g s ω) 2
      (unitSphereMeasure (m + 3)) :=
    fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k
  change (m + 2 : ℝ) *
      ‖sphereMeanZeroPart (m + 3)
        (scalarSphereFamilyTrace (m + 3) g hg r)‖ ^ 2 ≤
      unitSphereAngularEnergy (m + 3) (g r)
  have hGlobal := sharpUnitSpherePoincareLocal_to_global (m + 3) hLocal
  by_cases hr0 : r = 0
  · subst r
    have hSmooth : ContDiff ℝ 1 (g 0) := by
      have heq : g 0 = fun _ : GLEuclidean (m + 3) => (0 : ℝ) := by
        funext y
        simp [g, finiteBallSphereFamily_zero (m + 3) R hR z y]
      rw [heq]
      exact contDiff_const
    exact sphereTrace_angular_gap m hGlobal (g 0) hSmooth (hg 0)
  by_cases hrR : r = R
  · subst r
    have hSmooth : ContDiff ℝ 1 (g R) := by
      have heq : g R = fun y : GLEuclidean (m + 3) => y k := by
        funext y
        simp [g, finiteBallSphereFamily_outer (m + 3) R z y]
      rw [heq]
      simpa only [EuclideanSpace.coe_proj] using
        ((EuclideanSpace.proj k :
          GLEuclidean (m + 3) →L[ℝ] ℝ).contDiff :
            ContDiff ℝ 1 (EuclideanSpace.proj k))
    exact sphereTrace_angular_gap m hGlobal (g R) hSmooth (hg R)
  have hrInt : r ∈ Ioo (0 : ℝ) R :=
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),
      lt_of_le_of_ne hr.2 hrR⟩
  have hActual : MemLp
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (z (r • (ω : GLEuclidean (m + 3)))) k) 2
      (unitSphereMeasure (m + 3)) := by
    simpa only [g, finiteBallSphereFamily_interior
      (m + 3) R z r hrInt] using hg r
  have hgap := scaledPuncturedSphereTrace_angular_gap m hLocal
    R r hrInt z hz k hActual
  simpa only [g, scalarSphereFamilyTrace,
    finiteBallSphereFamily_interior (m + 3) R z r hrInt] using hgap

end

end BrezisOP6
