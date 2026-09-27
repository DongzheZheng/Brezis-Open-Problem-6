import BrezisOP6.SphereFiniteFamilyOuterL2

/-!
# Continuity of the actual finite-ball sphere trace up to the outer radius

The interior trace is differentiable as a Hilbert-valued map.  Its
separately proved left limit at the physical boundary joins these
local continuities into continuity on every positive closed annulus.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem finiteBallSphereFamily_trace_continuousOn_positive_annulus
    (n : ℕ) (R δ : ℝ) (hδ : 0 < δ) (hδR : δ < R)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n)
    (htrace : Tendsto
      (fun r => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r)
      (𝓝[<] R)
      (𝓝 (scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) R))) :
    ContinuousOn
      (fun r => scalarSphereFamilyTrace n
        (fun s y => (finiteBallSphereFamily n R z s y) k)
        (fun s => finiteBallSphereFamily_memLp n R z hz s k) r)
      (Icc δ R) := by
  let v : ℝ → UnitSphereL2 n :=
    fun r => scalarSphereFamilyTrace n
      (fun s y => (finiteBallSphereFamily n R z s y) k)
      (fun s => finiteBallSphereFamily_memLp n R z hz s k) r
  intro r hr
  by_cases hrR : r = R
  · subst r
    exact (continuousWithinAt_Icc_iff_Iic hδR).2
      (continuousWithinAt_Iio_iff_Iic.mp htrace)
  · have hrpos : 0 < r := lt_of_lt_of_le hδ hr.1
    have hrlt : r < R := lt_of_le_of_ne hr.2 hrR
    exact ((finiteBallSphereFamily_hasDerivAt_interior
      n R z hz r ⟨hrpos, hrlt⟩ k).continuousAt).continuousWithinAt

end

end BrezisOP6
