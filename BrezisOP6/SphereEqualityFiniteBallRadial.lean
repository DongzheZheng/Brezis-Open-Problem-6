import BrezisOP6.SphereEqualityFixedRadius

/-!
# Radial equality for the actual finite-ball sphere family

The abstract Hilbert equality theorem is applied to the concrete `C¹`
quotient slices.  The `L²` radial derivative is continuous on the open
radius interval.  Its mean-zero part vanishes almost everywhere at
quadratic-bridge equality, hence the mean-zero trace is constant.  A
left boundary trace identifies that constant with the actual outer trace.
-/

namespace BrezisOP6

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

theorem finiteBallSphereFamily_meanZeroPart_eq_outer
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (k : Fin n)
    (hderivZero : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) R)),
      finiteBallSphereFamilyRadialL2 n R z hz s k =
        sphereMeanCoefficient n
          (finiteBallSphereFamilyRadialL2 n R z hz s k) •
            unitSphereConstant n)
    (hOuterLimit : Tendsto
      (fun s => sphereMeanZeroPart n
        (scalarSphereFamilyTrace n
          (fun t y => (finiteBallSphereFamily n R z t y) k)
          (fun t => finiteBallSphereFamily_memLp n R z hz t k) s))
      (𝓝[<] R)
      (𝓝 (sphereMeanZeroPart n
        (scalarSphereFamilyTrace n
          (fun t y => (finiteBallSphereFamily n R z t y) k)
          (fun t => finiteBallSphereFamily_memLp n R z hz t k) R))))
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    sphereMeanZeroPart n
      (scalarSphereFamilyTrace n
        (fun t y => (finiteBallSphereFamily n R z t y) k)
        (fun t => finiteBallSphereFamily_memLp n R z hz t k) r) =
    sphereMeanZeroPart n
      (scalarSphereFamilyTrace n
        (fun t y => (finiteBallSphereFamily n R z t y) k)
        (fun t => finiteBallSphereFamily_memLp n R z hz t k) R) := by
  let g : ℝ → GLEuclidean n → ℝ :=
    fun t y => (finiteBallSphereFamily n R z t y) k
  let hg : ∀ t, MemLp
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 => g t ω)
      2 (unitSphereMeasure n) :=
    fun t => finiteBallSphereFamily_memLp n R z hz t k
  let v : ℝ → UnitSphereL2 n := scalarSphereFamilyTrace n g hg
  let dv : ℝ → UnitSphereL2 n :=
    fun t => finiteBallSphereFamilyRadialL2 n R z hz t k
  let c : ℝ → ℝ := fun t => sphereMeanCoefficient n (v t)
  let dc : ℝ → ℝ := fun t => sphereMeanCoefficient n (dv t)
  let e : UnitSphereL2 n := unitSphereConstant n
  have hv : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt v (dv t) t := by
    intro t ht
    exact finiteBallSphereFamily_hasDerivAt_interior n R z hz t ht k
  have hc : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt c (dc t) t := by
    intro t ht
    exact sphereMeanCoefficient_hasDerivAt n v t (dv t) (hv t ht)
  have hDvCont : ContinuousOn dv (Ioo (0 : ℝ) R) :=
    finiteBallSphereFamilyRadialL2_continuousOn n R z hz k
  have hMeanCont : Continuous (sphereMeanCoefficient n) := by
    unfold sphereMeanCoefficient
    fun_prop
  have hDcCont : ContinuousOn dc (Ioo (0 : ℝ) R) :=
    hMeanCont.comp_continuousOn hDvCont
  have hRemCont : ContinuousOn (fun t => dv t - dc t • e)
      (Ioo (0 : ℝ) R) :=
    hDvCont.sub (hDcCont.smul continuousOn_const)
  have hAE : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) R)),
      dv t = dc t • e := hderivZero
  have hconst : ∀ a ∈ Ioo (0 : ℝ) R,
      ∀ b ∈ Ioo (0 : ℝ) R,
        v a - c a • e = v b - c b • e := by
    intro a ha b hb
    exact radial_meanZero_part_constant_on_open
      e v dv c dc R hv hc hRemCont hAE a b ha hb
  have hlim : Tendsto (fun t => v t - c t • e)
      (𝓝[<] R) (𝓝 (v R - c R • e)) := hOuterLimit
  have hout := radial_constant_eq_outer_of_left_limit
    (fun t => v t - c t • e) R hR hconst hlim r hr
  exact hout

end

end BrezisOP6
