import BrezisOP6.EnergyIBP

/-!
# A single-point modification does not change the Euclidean GL energy

Away from the modified point the maps agree on a neighborhood, hence so do
their actual Fréchet derivatives. The remaining point has zero Euclidean
volume, also after restricting volume to a ball.
-/

namespace BrezisOP6

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- Agreement off the origin implies equality of actual Fréchet derivatives
at every nonzero spatial point. No differentiability hypothesis is needed:
Mathlib's `fderiv` is local even where it takes its default value. -/
theorem fderiv_eq_of_eq_off_origin
    (n : ℕ) (u v : GLEuclidean n → GLEuclidean n)
    (h : ∀ x, x ≠ 0 → u x = v x)
    (x : GLEuclidean n) (hx : x ≠ 0) :
    fderiv ℝ u x = fderiv ℝ v x := by
  have hnear : u =ᶠ[𝓝 x] v := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact h y hy
  exact hnear.fderiv_eq

/-- Changing the value of a field only at the origin leaves its concrete
Fréchet-derivative Ginzburg--Landau energy on every ball unchanged. -/
theorem euclideanBallEnergy_eq_of_eq_off_origin
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (u v : GLEuclidean n → GLEuclidean n)
    (h : ∀ x, x ≠ 0 → u x = v x) :
    euclideanBallEnergy n R u = euclideanBallEnergy n R v := by
  letI : NeZero n := ⟨by omega⟩
  have hne : ∀ᵐ x : GLEuclidean n ∂(volume : Measure (GLEuclidean n)),
      x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  unfold euclideanBallEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hne] with x hx
  have hval := h x hx
  have hderiv := fderiv_eq_of_eq_off_origin n u v h x hx
  simp only [euclideanGradientSq]
  rw [hval, hderiv]

end

end BrezisOP6
