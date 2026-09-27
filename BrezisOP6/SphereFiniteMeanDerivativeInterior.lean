import BrezisOP6.SphereFiniteFamily
import BrezisOP6.SphereBridgeIntegral

/-!
# Interior differentiability of the actual regularized sphere mean

The finite-ball `L²` trace has a proved radial derivative strictly inside
the ball.  The mean is a continuous linear functional on that Hilbert
space, and multiplying by radius gives the regularized zero mode.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem finiteBallSphereRadialMean_hasDerivAt_interior
    (n : ℕ) (R : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt
      (vectorSphereRadialMean n
        (finiteBallSphereFamily n R z)
        (fun s j => finiteBallSphereFamily_memLp n R z hz s j) k)
      (sphereMeanCoefficient n
          (scalarSphereFamilyTrace n
            (fun s y => (finiteBallSphereFamily n R z s y) k)
            (fun s => finiteBallSphereFamily_memLp n R z hz s k) r) +
        r * sphereMeanCoefficient n
          (finiteBallSphereFamilyRadialL2 n R z hz r k)) r := by
  let g := fun s y => (finiteBallSphereFamily n R z s y) k
  let hg := fun s => finiteBallSphereFamily_memLp n R z hz s k
  let v := scalarSphereFamilyTrace n g hg
  let dv := finiteBallSphereFamilyRadialL2 n R z hz r k
  have htrace : HasDerivAt v dv r :=
    finiteBallSphereFamily_hasDerivAt_interior n R z hz r hr k
  have hmean := sphereMeanCoefficient_hasDerivAt n v r dv htrace
  simpa [vectorSphereRadialMean, scalarSphereRadialMean, v, dv, g, hg]
    using (hasDerivAt_id r).mul hmean

end

end BrezisOP6
