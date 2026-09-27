import BrezisOP6.SphereUnitTraceNorm

/-!
# Continuous sphere traces are determined by their `L²` class

Mathlib's polar surface measure has positive measure on every nonempty
open sphere set.  Equality of continuous spherical traces in `L²` therefore
upgrades to pointwise equality on the actual geometric sphere.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

theorem unitSphereTrace_pointwise_eq_of_L2_eq
    (n : ℕ) (g h : GLEuclidean n → ℝ)
    (hgc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g ω))
    (hhc : Continuous (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => h ω))
    (hg : MemLp (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => g ω) 2 (unitSphereMeasure n))
    (hh : MemLp (fun ω : Metric.sphere
      (0 : GLEuclidean n) 1 => h ω) 2 (unitSphereMeasure n))
    (heq : unitSphereTrace n g hg = unitSphereTrace n h hh) :
    ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      g ω = h ω := by
  letI : (unitSphereMeasure n).IsOpenPosMeasure := by
    change ((volume : Measure (GLEuclidean n)).toSphere).IsOpenPosMeasure
    infer_instance
  have hAE : (fun ω : Metric.sphere (0 : GLEuclidean n) 1 => g ω)
      =ᵐ[unitSphereMeasure n]
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 => h ω) := by
    filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with ω hgo hho
    calc
      g ω = (unitSphereTrace n g hg) ω := hgo.symm
      _ = (unitSphereTrace n h hh) ω := by rw [heq]
      _ = h ω := hho
  have hAEUniv : (fun ω : Metric.sphere (0 : GLEuclidean n) 1 => g ω)
      =ᵐ[(unitSphereMeasure n).restrict univ]
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 => h ω) := by
    simpa using hAE
  have hEqOn := Measure.eqOn_open_of_ae_eq hAEUniv isOpen_univ
    hgc.continuousOn hhc.continuousOn
  intro ω
  exact hEqOn (mem_univ ω)

end

end BrezisOP6
