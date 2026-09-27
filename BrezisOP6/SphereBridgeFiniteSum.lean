import BrezisOP6.SphereBridgeIntegral

/-!
# Exact finite-coordinate decomposition of the spherical bridge

The quantitative annular estimate is obtained separately for each target
coordinate.  This identity identifies the sum of those scalar quadratic
forms with the vector quadratic form in the energy identity.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

theorem vectorSphereBridge_integral_eq_coordinate_sum
    (m : ℕ) (f F : ℝ → ℝ)
    (R : ℝ)
    (g : ℝ → EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 3)))
    (hg : ∀ (r : ℝ) (i : Fin (m + 3)),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => (g r ω) i) 2
          (unitSphereMeasure (m + 3)))
    (dv : ℝ → Fin (m + 3) → UnitSphereL2 (m + 3))
    (hfullInt : ∀ i : Fin (m + 3), IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s x => (g s x) i) (fun s => hg s i)
        (fun s => dv s i)) volume 0 R) :
    (∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F g hg dv r) =
      ∑ i : Fin (m + 3),
        ∫ r in (0 : ℝ)..R,
          scalarSphereBridgeDensity m f F
            (fun s x => (g s x) i) (fun s => hg s i)
            (fun s => dv s i) r := by
  simpa only [vectorSphereBridgeDensity] using
    (intervalIntegral.integral_finset_sum (s := Finset.univ)
      (f := fun i r => scalarSphereBridgeDensity m f F
        (fun s x => (g s x) i) (fun s => hg s i)
        (fun s => dv s i) r)
      (fun i _ => hfullInt i))

end

end BrezisOP6
