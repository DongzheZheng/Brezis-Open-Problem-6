import DeGiorgi.SobolevSpace.Approximation
import BrezisOP6.WeakBallEnergy

/-!
# Vector-valued weak gradients and scalar Sobolev witnesses

Each coordinate of a globally weakly differentiable Euclidean field gives a
scalar `W¹,²` witness. The same field coordinates lie in `L⁴`. This connects
the weak fixed-trace definition to the smooth approximation library.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace BrezisOP6

noncomputable section

private theorem compactSmooth_is_C1ScalarCompactTest
    {n : ℕ} {φ : GLEuclidean n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcompact : HasCompactSupport φ) :
    C1ScalarCompactTest n φ := by
  obtain ⟨r, hr⟩ := hcompact.isCompact.isBounded.subset_ball (0 : GLEuclidean n)
  refine ⟨hφ.of_le (by simp), max r 0, le_max_right r 0, ?_⟩
  intro x hx
  have hxnot : x ∉ tsupport φ := by
    intro hxm
    have hlt : ‖x‖ < r := by
      simpa [Metric.mem_ball, dist_zero_right] using hr hxm
    exact (not_lt_of_ge (le_trans (le_max_left r 0) hx)) hlt
  exact image_eq_zero_of_notMem_tsupport hxnot

/-- Every coordinate of the global vector distributional gradient is a
    scalar weak partial derivative in the DeGiorgi Sobolev interface. -/
theorem HasGlobalWeakGradient.component_weakPartialDeriv
    {n : ℕ} {u : GLEuclidean n → GLEuclidean n}
    {G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n}
    (h : HasGlobalWeakGradient n u G) (j i : Fin n) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (G x (EuclideanSpace.single i (1 : ℝ))) j)
      (fun x => (u x) j) Set.univ := by
  intro φ hφ hφcompact _
  let P : GLEuclidean n →L[ℝ] ℝ := EuclideanSpace.proj j
  have ht : C1ScalarCompactTest n φ :=
    compactSmooth_is_C1ScalarCompactTest hφ hφcompact
  obtain ⟨hleft, hright, hweak⟩ := h.2.2.2.2.2 φ ht i
  have hleftP := P.integral_comp_comm hleft
  have hrightP := P.integral_comp_comm hright
  simp only [MeasureTheory.setIntegral_univ] at *
  calc
    ∫ x, (u x) j * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
        = ∫ x, P ((fderiv ℝ φ x) (EuclideanSpace.single i 1) • u x) := by
            congr 1
            funext x
            simp [P, mul_comm]
    _ = P (∫ x, (fderiv ℝ φ x) (EuclideanSpace.single i 1) • u x) := hleftP
    _ = P (-(∫ x, φ x • G x (EuclideanSpace.single i 1))) := by rw [hweak]
    _ = -(∫ x, P (φ x • G x (EuclideanSpace.single i 1))) := by
          rw [map_neg, ← hrightP]
    _ = -∫ x, ((G x (EuclideanSpace.single i 1)) j) * φ x := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          simp [P, mul_comm]

/-- The coordinate fields inherit both relevant Lebesgue exponents from the
    vector-valued zero-trace certificate. -/
theorem HasGlobalWeakGradient.component_memLp_two
    {n : ℕ} {u : GLEuclidean n → GLEuclidean n}
    {G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n}
    (h : HasGlobalWeakGradient n u G) (j : Fin n) :
    MemLp (fun x => (u x) j) 2 volume := by
  have hvec : MemLp u 2 volume :=
    (memLp_two_iff_integrable_sq_norm h.1).2 h.2.2.1
  have hcoord : AEStronglyMeasurable (fun x => (u x) j) volume := by
    exact (EuclideanSpace.proj j).continuous.aestronglyMeasurable.comp_aemeasurable h.1.aemeasurable
  exact hvec.of_le hcoord
    (Filter.Eventually.of_forall fun x => PiLp.norm_apply_le (u x) j)

theorem HasGlobalWeakGradient.component_memLp_four
    {n : ℕ} {u : GLEuclidean n → GLEuclidean n}
    {G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n}
    (h : HasGlobalWeakGradient n u G) (j : Fin n) :
    MemLp (fun x => (u x) j) 4 volume := by
  have hvec : MemLp u 4 volume := by
    exact (integrable_norm_rpow_iff h.1 (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).mp (by simpa using h.2.2.2.1)
  have hcoord : AEStronglyMeasurable (fun x => (u x) j) volume := by
    exact (EuclideanSpace.proj j).continuous.aestronglyMeasurable.comp_aemeasurable h.1.aemeasurable
  exact hvec.of_le hcoord
    (Filter.Eventually.of_forall fun x => PiLp.norm_apply_le (u x) j)

/-- The Hilbert--Schmidt square-integrability field supplies the missing
    scalar weak-gradient components without an added Sobolev hypothesis. -/
theorem HasGlobalWeakGradient.gradient_component_memLp_two
    {n : ℕ} {u : GLEuclidean n → GLEuclidean n}
    {G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n}
    (h : HasGlobalWeakGradient n u G) (j i : Fin n) :
    MemLp (fun x => (G x (EuclideanSpace.single i (1 : ℝ))) j) 2 volume := by
  let ei : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
  let ev : (GLEuclidean n →L[ℝ] GLEuclidean n) →L[ℝ] GLEuclidean n :=
    ContinuousLinearMap.apply ℝ (GLEuclidean n) ei
  have hGiAES : AEStronglyMeasurable (fun x => G x ei) volume := by
    exact ev.continuous.aestronglyMeasurable.comp_aemeasurable h.2.1.aemeasurable
  have hGiSq : Integrable (fun x => ‖G x ei‖ ^ 2) volume := by
    apply Integrable.mono_nonneg h.2.2.2.2.1 (hGiAES.norm.pow 2)
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · exact Filter.Eventually.of_forall fun x => by
        change ‖G x ei‖ ^ 2 ≤ ∑ k : Fin n,
          ‖G x (EuclideanSpace.single k (1 : ℝ))‖ ^ 2
        exact Finset.single_le_sum
          (f := fun k : Fin n => ‖G x (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
          (fun k hk => sq_nonneg _) (Finset.mem_univ i)
  have hGiMemLp : MemLp (fun x => G x ei) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hGiAES).2 hGiSq
  have hcoordAES : AEStronglyMeasurable (fun x => (G x ei) j) volume := by
    exact (EuclideanSpace.proj j).continuous.aestronglyMeasurable.comp_aemeasurable
      hGiAES.aemeasurable
  exact hGiMemLp.of_le hcoordAES
    (Filter.Eventually.of_forall fun x => PiLp.norm_apply_le (G x ei) j)

/-- A complete scalar Sobolev witness for each output coordinate of the
    vector field.  Its displayed gradient equals the given certified
    distributional gradient component by component. -/
noncomputable def HasGlobalWeakGradient.component_W12Witness
    {n : ℕ} [NeZero n] {u : GLEuclidean n → GLEuclidean n}
    {G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n}
    (h : HasGlobalWeakGradient n u G) (j : Fin n) :
    DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (fun x => (u x) j) Set.univ where
  memLp := by
    simpa [Measure.restrict_univ] using h.component_memLp_two j
  weakGrad := fun x => WithLp.toLp 2 (fun i => (G x (EuclideanSpace.single i (1 : ℝ))) j)
  weakGrad_component_memLp := by
    intro i
    simpa [Measure.restrict_univ] using h.gradient_component_memLp_two j i
  isWeakGrad := by
    intro i
    simpa using h.component_weakPartialDeriv j i

end

end BrezisOP6
