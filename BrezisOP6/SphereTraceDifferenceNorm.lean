import BrezisOP6.SphereUnitTraceNorm

/-!
# A vector sphere trace difference is its physical surface distance

This elementary identity connects the Hilbert-space trace estimates in the
quadratic bridge with the squared Euclidean distance between two fields on
each sphere.  Both sides use the same representatives, and all target
coordinates are summed before the surface integral is taken.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

theorem vectorSphereTrace_difference_norm_sq_eq_integral
    (n : ℕ) (g h : GLEuclidean n → GLEuclidean n)
    (hg : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (g ω) k) 2 (unitSphereMeasure n))
    (hh : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (h ω) k) 2 (unitSphereMeasure n))
    (hgc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g ω))
    (hhc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => h ω)) :
    (∑ k : Fin n,
      ‖vectorSphereTrace n g hg k - vectorSphereTrace n h hh k‖ ^ 2) =
      ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        ‖g ω - h ω‖ ^ 2 ∂(unitSphereMeasure n) := by
  let d : GLEuclidean n → GLEuclidean n := fun x => g x - h x
  have hd : ∀ k : Fin n,
      MemLp (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (d ω) k) 2 (unitSphereMeasure n) := by
    intro k
    simpa only [d, Pi.sub_apply] using (hg k).sub (hh k)
  have hdc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => d ω) := hgc.sub hhc
  have hTrace (k : Fin n) :
      vectorSphereTrace n d hd k =
        vectorSphereTrace n g hg k - vectorSphereTrace n h hh k := by
    exact (hg k).toLp_sub (hh k)
  calc
    (∑ k : Fin n,
        ‖vectorSphereTrace n g hg k - vectorSphereTrace n h hh k‖ ^ 2) =
      vectorSphereL2Sq n (vectorSphereTrace n d hd) := by
        simp only [vectorSphereL2Sq, hTrace]
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ‖d ω‖ ^ 2 ∂(unitSphereMeasure n) :=
      vectorSphereTrace_total_norm_sq_eq_integral n d hd hdc
    _ = _ := rfl

end

end BrezisOP6
