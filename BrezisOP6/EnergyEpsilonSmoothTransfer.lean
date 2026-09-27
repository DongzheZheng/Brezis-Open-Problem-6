import BrezisOP6.EnergyEpsilonScaling
import BrezisOP6.SmoothEnergyClosure

/-!
# Fixed-trace smooth comparison at arbitrary coherence length

The integral scaling theorem is used here to transport an actual smooth
unit-parameter minimum to every positive `ε`.  The unit-parameter theorem
is the mathematical input; neither the energy identity nor boundary trace
compatibility is postulated.
-/

namespace BrezisOP6

open Metric

noncomputable section

/-- Scaling a smooth finite-ball competitor preserves the boundary condition
with the correctly scaled radial profile. -/
theorem smoothBallCompetitor_dilate (m : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hv : SmoothBallCompetitor m R f v) :
    SmoothBallCompetitor m (R / ε) (fun r => f (ε * r))
      (fun x => v (ε • x)) := by
  constructor
  · exact hv.1.comp (contDiff_const_smul ε)
  · intro x hx
    have hnorm : ‖ε • x‖ = R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, hx]
      field_simp [hε.ne']
    change v (ε • x) = _
    rw [hv.2 (ε • x) hnorm]
    exact radialVortex_dilate (m + 3) ε hε f x

/-- An established smooth minimum at `ε=1`, applied on the dilated ball,
gives the smooth finite-ball minimum for any `ε>0`. -/
theorem smoothBallEpsilonMinimum_of_unitMinimum
    (m : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ)
    (hunit : ∀ w : GLEuclidean (m + 3) → GLEuclidean (m + 3),
      SmoothBallCompetitor m (R / ε) (fun r => f (ε * r)) w →
        euclideanBallEnergy (m + 3) (R / ε)
            (radialVortex (m + 3) (fun r => f (ε * r))) ≤
          euclideanBallEnergy (m + 3) (R / ε) w)
    (v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hv : SmoothBallCompetitor m R f v) :
    euclideanBallEnergyEpsilon (m + 3) R ε (radialVortex (m + 3) f) ≤
      euclideanBallEnergyEpsilon (m + 3) R ε v := by
  apply (euclideanBallEnergyEpsilon_le_iff_dilate (m + 3) R ε hε
    (radialVortex (m + 3) f) v).2
  have hcomp := hunit (fun x => v (ε • x))
    (smoothBallCompetitor_dilate m R ε hε f v hv)
  have hvortex :
      (fun x => radialVortex (m + 3) f (ε • x)) =
        radialVortex (m + 3) (fun r => f (ε * r)) := by
    funext x
    exact radialVortex_dilate (m + 3) ε hε f x
  rw [hvortex]
  exact hcomp

end

end BrezisOP6
