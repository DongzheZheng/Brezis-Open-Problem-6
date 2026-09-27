import BrezisOP6.WeakBallEnergy

/-!
# Finite-coordinate control of Euclidean `Lᵖ` norms

The density argument first approximates every scalar output coordinate and
every scalar component of the gradient.  This lemma converts those finitely
many bounds into the vector-valued norm required by the paper's energy.
-/

namespace BrezisOP6

open MeasureTheory
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 2000000

theorem eLpNorm_euclidean_le_sum_coordinates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (n : ℕ) (v : α → GLEuclidean n) (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hcoord : ∀ i : Fin n,
      AEStronglyMeasurable (fun x => (v x) i) μ) :
    eLpNorm v p μ ≤
      ∑ i : Fin n, eLpNorm (fun x => (v x) i) p μ := by
  let e (i : Fin n) : GLEuclidean n :=
    EuclideanSpace.single i (1 : ℝ)
  let w (i : Fin n) (x : α) : GLEuclidean n := (v x) i • e i
  have hv (x : α) : v x = ∑ i : Fin n, (v x) i • e i := by
    simpa only [e, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (v x)).symm
  have hwmeas (i : Fin n) : AEStronglyMeasurable (w i) μ :=
    (hcoord i).smul_const (e i)
  have hterm (i : Fin n) :
      eLpNorm (w i) p μ =
        eLpNorm (fun x => (v x) i) p μ := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [] with x
    simp only [w, norm_smul, e, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs]
  have hsum :
      eLpNorm (fun x => ∑ i : Fin n, w i x) p μ ≤
        ∑ i : Fin n, eLpNorm (w i) p μ := by
    have hfun : (∑ i : Fin n, w i) =
        fun x => ∑ i : Fin n, w i x := by
      funext x
      simp only [Finset.sum_apply]
    rw [← hfun]
    exact eLpNorm_sum_le (μ := μ) (p := p)
      (s := Finset.univ) (f := w) (fun i _ => hwmeas i) hp
  calc
    eLpNorm v p μ =
        eLpNorm (fun x => ∑ i : Fin n, w i x) p μ := by
          apply eLpNorm_congr_ae
          filter_upwards [] with x
          exact (hv x).trans (by rfl)
    _ ≤ ∑ i : Fin n,
        eLpNorm (w i) p μ := hsum
    _ = ∑ i : Fin n,
        eLpNorm (fun x => (v x) i) p μ := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i

/-- The real-valued form used for the weak-gradient components.  Requiring
actual `MemLp` coordinates ensures that `lpNorm` has its intended
non-totalized value. -/
theorem lpNorm_euclidean_le_sum_coordinates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (n : ℕ) (v : α → GLEuclidean n) (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hcoord : ∀ i : Fin n, MemLp (fun x => (v x) i) p μ) :
    lpNorm v p μ ≤
      ∑ i : Fin n, lpNorm (fun x => (v x) i) p μ := by
  let e (i : Fin n) : GLEuclidean n :=
    EuclideanSpace.single i (1 : ℝ)
  let w (i : Fin n) (x : α) : GLEuclidean n := (v x) i • e i
  have hv (x : α) : v x = ∑ i : Fin n, w i x := by
    simpa only [w, e, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (v x)).symm
  have htermENN (i : Fin n) :
      eLpNorm (w i) p μ =
        eLpNorm (fun x => (v x) i) p μ := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [] with x
    simp only [w, norm_smul, e, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs]
  have hwMem (i : Fin n) : MemLp (w i) p μ :=
    ⟨(hcoord i).aestronglyMeasurable.smul_const (e i), by
      rw [htermENN i]
      exact (hcoord i).2⟩
  have hterm (i : Fin n) :
      lpNorm (w i) p μ =
        lpNorm (fun x => (v x) i) p μ := by
    rw [← toReal_eLpNorm (hwMem i).aestronglyMeasurable,
      ← toReal_eLpNorm (hcoord i).aestronglyMeasurable,
      htermENN]
  have hfun : (∑ i : Fin n, w i) =
      fun x => ∑ i : Fin n, w i x := by
    funext x
    simp only [Finset.sum_apply]
  have hsum :
      lpNorm (fun x => ∑ i : Fin n, w i x) p μ ≤
        ∑ i : Fin n, lpNorm (w i) p μ := by
    rw [← hfun]
    exact lpNorm_sum_le (μ := μ) (p := p)
      (s := Finset.univ) (f := w) (fun i _ => hwMem i) hp
  calc
    lpNorm v p μ =
        lpNorm (fun x => ∑ i : Fin n, w i x) p μ := by
          congr 1
          funext x
          exact hv x
    _ ≤ ∑ i : Fin n, lpNorm (w i) p μ := hsum
    _ = ∑ i : Fin n,
        lpNorm (fun x => (v x) i) p μ := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i

end

end BrezisOP6
