import BrezisOP6.SphereTraceInjective
import BrezisOP6.BridgeEqualityL2Norm

/-!
# Fixed-radius rigidity of unit-sphere-valued traces

At a fixed radius, the equality bridge freezes the mean-zero part of
the `L²` trace.  The unit-length constraint fixes its total `L²` norm.
The Pythagorean budget then eliminates every added constant mode, and
full support of the polar sphere measure upgrades `L²` equality to a
pointwise identity.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

theorem sphereValued_trace_eq_of_meanZeroPart_eq
    (n : ℕ) (hn : 1 ≤ n)
    (g h : GLEuclidean n → GLEuclidean n)
    (hg : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (g ω) k) 2 (unitSphereMeasure n))
    (hh : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (h ω) k) 2 (unitSphereMeasure n))
    (hgc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g ω))
    (hhc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => h ω))
    (hunitg : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ‖g ω‖ = 1)
    (hunith : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ‖h ω‖ = 1)
    (hMeanH : ∀ k : Fin n,
      sphereMeanCoefficient n (vectorSphereTrace n h hh k) = 0)
    (hparts : ∀ k : Fin n,
      sphereMeanZeroPart n (vectorSphereTrace n g hg k) =
        vectorSphereTrace n h hh k) :
    ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      g ω = h ω := by
  let v : Fin n → UnitSphereL2 n := vectorSphereTrace n g hg
  let w : Fin n → UnitSphereL2 n := vectorSphereTrace n h hh
  let c : Fin n → ℝ := fun k => sphereMeanCoefficient n (v k)
  have he : ‖unitSphereConstant n‖ = 1 :=
    unitSphereConstant_norm n hn
  have hw (k : Fin n) : inner ℝ (w k) (unitSphereConstant n) = 0 :=
    hMeanH k
  have hpart (k : Fin n) :
      v k - c k • unitSphereConstant n = w k :=
    hparts k
  have hnorm : (∑ k : Fin n, ‖v k‖ ^ 2) =
      ∑ k : Fin n, ‖w k‖ ^ 2 :=
    vectorSphereTrace_total_norm_sq_eq_of_unit_fields
      n g h hg hh hgc hhc hunitg hunith
  have htr := meanZero_traces_equal_of_fixed_total_norm
    n (unitSphereConstant n) v w c he hw hpart hnorm
  intro ω
  ext k
  exact unitSphereTrace_pointwise_eq_of_L2_eq n
    (fun x => (g x) k) (fun x => (h x) k)
    ((EuclideanSpace.proj k).continuous.comp hgc)
    ((EuclideanSpace.proj k).continuous.comp hhc)
    (hg k) (hh k) (htr k) ω

end

end BrezisOP6
