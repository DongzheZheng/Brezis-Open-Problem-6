import BrezisOP6.SphereRealization

/-!
# The angular bridge for an actual vector field

Each target coordinate of a map `ℝⁿ → ℝⁿ` is restricted to the Euclidean
unit sphere and placed in its real `L²` Hilbert space.  Summing the concrete
scalar sphere bridge over `Fin n` gives the vector-valued angular gap.  The
angular energy is the sum of the squared tangential derivatives of the
actual target coordinates.  The only spectral input is the exact sharp
Poincaré statement `SharpUnitSpherePoincare` from `SphereRealization`.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

/-- The vector-valued tangential Dirichlet energy, expressed in ordinary
Euclidean target coordinates. -/
def vectorSphereAngularEnergy (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, unitSphereAngularEnergy n (fun x => (g x) i)

/-- The `i`th coordinate of an actual vector field, as a sphere `L²` field. -/
def vectorSphereTrace (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ i : Fin n,
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 => (g ω) i) 2
          (unitSphereMeasure n))
    (i : Fin n) : UnitSphereL2 n :=
  unitSphereTrace n (fun x => (g x) i) (hg i)

/-- Squared `L²` size of all target coordinates on a sphere slice. -/
def vectorSphereL2Sq (n : ℕ) (v : Fin n → UnitSphereL2 n) : ℝ :=
  ∑ i : Fin n, ‖v i‖ ^ 2

/-- Squared size of the vector spherical mean. -/
def vectorSphereMeanSq (n : ℕ) (v : Fin n → UnitSphereL2 n) : ℝ :=
  ∑ i : Fin n, (sphereMeanCoefficient n (v i)) ^ 2

/-- Sum of the concrete scalar bridge gaps over all target coordinates.
`dv` is the radial derivative of each sphere `L²` slice when such a
derivative exists; no derivative existence is needed for this pointwise
algebraic inequality. -/
def vectorSphereBridgeGap (m : ℕ)
    (g : EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 3)))
    (hg : ∀ i : Fin (m + 3),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => (g ω) i) 2
          (unitSphereMeasure (m + 3)))
    (dv : Fin (m + 3) → UnitSphereL2 (m + 3))
    (r d : ℝ) : ℝ :=
  ∑ i : Fin (m + 3),
    (r ^ (m + 2) * d * ‖dv i‖ ^ 2 +
      r ^ m * d *
        (unitSphereAngularEnergy (m + 3) (fun x => (g x) i) -
          (m + 2 : ℝ) * ‖vectorSphereTrace (m + 3) g hg i‖ ^ 2) -
      (r ^ (m + 2) * d *
            (sphereMeanCoefficient (m + 3) (dv i)) ^ 2 -
        (m + 2 : ℝ) * r ^ m * d *
          (sphereMeanCoefficient (m + 3)
            (vectorSphereTrace (m + 3) g hg i)) ^ 2))

/-- The coordinatewise expression regroups into one vector angular energy,
one vector radial norm, and the vector spherical mean contribution. -/
theorem vectorSphereBridgeGap_eq_aggregate
    (m : ℕ)
    (g : EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 3)))
    (hg : ∀ i : Fin (m + 3),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => (g ω) i) 2
          (unitSphereMeasure (m + 3)))
    (dv : Fin (m + 3) → UnitSphereL2 (m + 3))
    (r d : ℝ) :
    vectorSphereBridgeGap m g hg dv r d =
      r ^ (m + 2) * d * vectorSphereL2Sq (m + 3) dv +
        r ^ m * d *
          (vectorSphereAngularEnergy (m + 3) g -
            (m + 2 : ℝ) *
              vectorSphereL2Sq (m + 3)
                (vectorSphereTrace (m + 3) g hg)) -
        (r ^ (m + 2) * d * vectorSphereMeanSq (m + 3) dv -
          (m + 2 : ℝ) * r ^ m * d *
            vectorSphereMeanSq (m + 3)
              (vectorSphereTrace (m + 3) g hg)) := by
  simp only [vectorSphereBridgeGap, vectorSphereL2Sq,
    vectorSphereMeanSq, vectorSphereAngularEnergy,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The full vector angular bridge dominates its vector zero-mode part.
The sharp Poincaré input concerns the actual Euclidean unit sphere; it
does not assert bridge positivity. -/
theorem vectorSphereBridgeGap_nonneg
    (m : ℕ) (hPoincare : SharpUnitSpherePoincare (m + 3))
    (g : EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 3)))
    (hSmooth : ∀ i : Fin (m + 3),
      ContDiff ℝ 1 (fun x => (g x) i))
    (hg : ∀ i : Fin (m + 3),
      MemLp (fun ω : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 3))) 1 => (g ω) i) 2
          (unitSphereMeasure (m + 3)))
    (dv : Fin (m + 3) → UnitSphereL2 (m + 3))
    (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    0 ≤ vectorSphereBridgeGap m g hg dv r d := by
  unfold vectorSphereBridgeGap
  apply Finset.sum_nonneg
  intro i hi
  exact sphereBridgeSlice_sub_mean_nonneg m hPoincare
    (fun x => (g x) i) (hSmooth i) (hg i) (dv i) r d hr hd

/-- The named angular energy is exactly the finite sum used by the vector
bridge.  In particular, it is a concrete target-coordinate realization of
the `angular` parameter in `bridgeQuadraticDensity`. -/
theorem vectorSphereAngularEnergy_eq_sum (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    vectorSphereAngularEnergy n g =
      ∑ i : Fin n, unitSphereAngularEnergy n (fun x => (g x) i) := rfl

end

end BrezisOP6
