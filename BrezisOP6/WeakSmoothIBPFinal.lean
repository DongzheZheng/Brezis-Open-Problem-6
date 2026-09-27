import BrezisOP6.WeakSmoothIBPReduction

/-!
# Classical derivatives are distributional derivatives on the ball

The proof uses Mathlib's Bochner-valued integration-by-parts theorem for
directional Fréchet derivatives.  The compact-support localization follows
the method of Armstrong--Kempe, `DeGiorgi/SobolevSpace/WeakDerivatives.lean`
(Apache-2.0), adapted here to vector-valued fields and to our finite-ball
test interface.  No source code from that project is copied.
-/

namespace BrezisOP6

open MeasureTheory Metric Function

noncomputable section

/-- A `C¹` test vanishing beyond an interior radius has compact support,
and its topological support lies inside the open ball. -/
theorem c1ScalarInteriorTest_compactSupport_and_subset_ball
    (n : ℕ) (R : ℝ) (φ : GLEuclidean n → ℝ)
    (hφ : C1ScalarInteriorTest n R φ) :
    HasCompactSupport φ ∧
      tsupport φ ⊆ Metric.ball (0 : GLEuclidean n) R := by
  obtain ⟨ρ, hρnonneg, hρR, hzero⟩ := hφ.2
  have hclosed : support φ ⊆ Metric.closedBall
      (0 : GLEuclidean n) ρ := by
    intro x hx
    by_contra hnot
    have hρx : ρ < ‖x‖ := by
      have hnotLe : ¬ ‖x‖ ≤ ρ := by
        intro hle
        exact hnot (by simpa only [Metric.mem_closedBall,
          dist_zero_right] using hle)
      exact lt_of_not_ge hnotLe
    exact (mem_support.mp hx) (hzero x hρx.le)
  have htsupport : tsupport φ ⊆ Metric.closedBall
      (0 : GLEuclidean n) ρ :=
    closure_minimal hclosed isClosed_closedBall
  constructor
  · apply HasCompactSupport.intro'
      (isCompact_closedBall (0 : GLEuclidean n) ρ)
      isClosed_closedBall
    intro x hx
    have hρx : ρ < ‖x‖ := by
      have hnotLe : ¬ ‖x‖ ≤ ρ := by
        intro hle
        exact hx (by simpa only [Metric.mem_closedBall,
          dist_zero_right] using hle)
      exact lt_of_not_ge hnotLe
    exact hzero x hρx.le
  · intro x hx
    have hnorm : ‖x‖ ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        htsupport hx
    have hlt : ‖x‖ < R := lt_of_le_of_lt hnorm hρR
    simpa only [Metric.mem_ball, dist_zero_right] using hlt

/-- The usual multidimensional integration by parts, now in the exact
vector-valued and restricted-ball form used by `HasWeakGradientOnBall`. -/
theorem hasWeakGradientOnBall_of_globalC1
    (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u) :
    HasWeakGradientOnBall n R u (fderiv ℝ u) := by
  intro φ hφ i
  let v : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
  obtain ⟨hφCompact, hφSupport⟩ :=
    c1ScalarInteriorTest_compactSupport_and_subset_ball n R φ hφ
  have hφDerivCompact : HasCompactSupport
      (fun x => (fderiv ℝ φ x) v) :=
    hφCompact.fderiv_apply (𝕜 := ℝ) v
  have hφDerivSupport :
      tsupport (fun x => (fderiv ℝ φ x) v) ⊆
        Metric.ball (0 : GLEuclidean n) R :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφSupport
  have hφcont : Continuous φ := hφ.1.continuous
  have hucont : Continuous u := hu.continuous
  have hφdcont : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hudcont : Continuous (fun x => (fderiv ℝ u x) v) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hAFull : Integrable
      (fun x => (fderiv ℝ φ x) v • u x) volume :=
    (hφdcont.smul hucont).integrable_of_hasCompactSupport
      hφDerivCompact.smul_right
  have hBFull : Integrable
      (fun x => φ x • (fderiv ℝ u x) v) volume :=
    (hφcont.smul hudcont).integrable_of_hasCompactSupport
      hφCompact.smul_right
  have hCFull : Integrable (fun x => φ x • u x) volume :=
    (hφcont.smul hucont).integrable_of_hasCompactSupport
      hφCompact.smul_right
  have hOutsideA : ∀ x : GLEuclidean n,
      x ∉ Metric.ball (0 : GLEuclidean n) R →
      (fderiv ℝ φ x) v • u x = 0 := by
    intro x hx
    have hnot : x ∉ tsupport (fun y => (fderiv ℝ φ y) v) :=
      fun h => hx (hφDerivSupport h)
    have hzero : (fderiv ℝ φ x) v = 0 :=
      notMem_support.mp (fun hs => hnot (subset_tsupport _ hs))
    simp [hzero]
  have hOutsideB : ∀ x : GLEuclidean n,
      x ∉ Metric.ball (0 : GLEuclidean n) R →
      φ x • (fderiv ℝ u x) v = 0 := by
    intro x hx
    have hnot : x ∉ tsupport φ := fun h => hx (hφSupport h)
    have hzero : φ x = 0 :=
      notMem_support.mp (fun hs => hnot (subset_tsupport _ hs))
    simp [hzero]
  have hARestr : Integrable
      (fun x => (fderiv ℝ φ x) v • u x)
      (weakBallMeasure n R) := hAFull.integrableOn
  have hBRestr : Integrable
      (fun x => φ x • (fderiv ℝ u x) v)
      (weakBallMeasure n R) := hBFull.integrableOn
  refine ⟨hARestr, hBRestr, ?_⟩
  have hAeq :
      (∫ x, (fderiv ℝ φ x) v • u x ∂(weakBallMeasure n R)) =
        ∫ x, (fderiv ℝ φ x) v • u x ∂volume := by
    change (∫ x in Metric.ball (0 : GLEuclidean n) R,
      (fderiv ℝ φ x) v • u x) = _
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hOutsideA
  have hBeq :
      (∫ x, φ x • (fderiv ℝ u x) v ∂(weakBallMeasure n R)) =
        ∫ x, φ x • (fderiv ℝ u x) v ∂volume := by
    change (∫ x in Metric.ball (0 : GLEuclidean n) R,
      φ x • (fderiv ℝ u x) v) = _
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hOutsideB
  have hIBP :
      (∫ x, φ x • (fderiv ℝ u x) v ∂volume) =
        -(∫ x, (fderiv ℝ φ x) v • u x ∂volume) :=
    integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      hAFull hBFull hCFull
      (fun x _ => hφ.1.differentiable_one x)
      (fun x _ => hu.differentiable_one x)
  simp only [v] at hAeq hBeq hIBP ⊢
  rw [hAeq, hBeq]
  calc
    (∫ x, (fderiv ℝ φ x)
      (EuclideanSpace.single i (1 : ℝ)) • u x ∂volume) =
        -(-(∫ x, (fderiv ℝ φ x)
          (EuclideanSpace.single i (1 : ℝ)) • u x ∂volume)) := by
          simp
    _ = -(∫ x, φ x • (fderiv ℝ u x)
      (EuclideanSpace.single i (1 : ℝ)) ∂volume) := by
        rw [hIBP]

/-- A globally `C¹` map on a finite ball has its canonical, unconditional
`H¹∩L⁴` weak-gradient certificate. -/
def WeakH1L4BallField.ofGlobalC1
    (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u) :
    WeakH1L4BallField n R :=
  WeakH1L4BallField.ofGlobalC1_of_derivative_integral_zero n R u hu
    (by
      intro φ hφ i
      have hweak := hasWeakGradientOnBall_of_globalC1 n R u hu
      have hraw := hweak φ hφ i
      -- The product derivative integral is the sum of the two integrals
      -- just shown to cancel.  This follows from the pointwise product rule.
      have hpoint (x : GLEuclidean n) :
          (fderiv ℝ (fun y => φ y • u y) x)
            (EuclideanSpace.single i (1 : ℝ)) =
          (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x +
            φ x • (fderiv ℝ u x)
              (EuclideanSpace.single i (1 : ℝ)) :=
        classical_scalar_vector_test_product_rule n φ u x i
          (hφ.1.differentiable_one x) (hu.differentiable_one x)
      simp_rw [hpoint]
      rw [integral_add hraw.1 hraw.2.1]
      exact add_eq_zero_iff_eq_neg.mpr hraw.2.2)

end

end BrezisOP6
