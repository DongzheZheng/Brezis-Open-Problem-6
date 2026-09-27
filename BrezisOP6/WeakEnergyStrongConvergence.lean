import BrezisOP6.WeakBallEnergy

/-!
# Strong convergence and weak ball energy

This module isolates the continuous polynomial part of the Sobolev closure
argument.  It does not assert the trace-preserving smooth-density theorem.
-/

namespace BrezisOP6

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

noncomputable section

private theorem integral_norm_pow_eq_lpNorm_pow
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (p : ℕ) (hp : p ≠ 0)
    (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (∫ x, ‖f x‖ ^ p ∂μ) = (lpNorm f p μ) ^ p := by
  have hrew := lpNorm_nnreal_eq_integral_norm_rpow
    (p := (p : ℝ≥0)) (by exact_mod_cast hp) hf
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ := by
    apply integral_nonneg
    intro x
    positivity
  have hrew' : lpNorm f (p : ℝ≥0∞) μ =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ ((p : ℝ)⁻¹) := by
    simpa using hrew
  rw [hrew']
  simpa using (Real.rpow_inv_natCast_pow hnonneg hp).symm

/-- The real-valued `Lᵖ` norm is continuous under strong `Lᵖ` convergence.
All functions are required to belong to `Lᵖ`; this avoids the totalized
value of `lpNorm` on nonmeasurable or nonintegrable functions. -/
private theorem tendsto_lpNorm_of_tendsto_lpNorm_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {ι : Type*} {l : Filter ι}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : ι → α → E) (g : α → E)
    (hf : ∀ j, MemLp (f j) p μ) (hg : MemLp g p μ)
    (hconv : Tendsto (fun j => lpNorm (f j - g) p μ) l (nhds 0)) :
    Tendsto (fun j => lpNorm (f j) p μ) l (nhds (lpNorm g p μ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (j : ι) :
      |lpNorm (f j) p μ - lpNorm g p μ| ≤ lpNorm (f j - g) p μ := by
    apply abs_le.mpr
    constructor
    · have h := lpNorm_le_lpNorm_add_lpNorm_sub
        (f := g) (g := f j) (hf j) hp
      linarith
    · have h := lpNorm_le_lpNorm_add_lpNorm_sub'
        (f := f j) (g := g) hg hp
      linarith
  have hlim : Tendsto
      (fun j => |lpNorm (f j) p μ - lpNorm g p μ|) l (nhds 0) :=
    squeeze_zero (fun j => abs_nonneg _) hbound hconv
  simpa [Real.dist_eq] using hlim

/-- Strong `Lᵖ` convergence implies convergence of its `p`th moment. -/
theorem integral_norm_pow_tendsto_of_strongLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {ι : Type*} {l : Filter ι}
    (p : ℕ) (hp : p ≠ 0) (hp1 : 1 ≤ (p : ℝ≥0∞))
    (f : ι → α → E) (g : α → E)
    (hf : ∀ j, MemLp (f j) p μ) (hg : MemLp g p μ)
    (hconv : Tendsto (fun j => lpNorm (f j - g) p μ) l (nhds 0)) :
    Tendsto (fun j => ∫ x, ‖f j x‖ ^ p ∂μ) l
      (nhds (∫ x, ‖g x‖ ^ p ∂μ)) := by
  have hnorm := tendsto_lpNorm_of_tendsto_lpNorm_sub
    (p := (p : ℝ≥0∞)) (by simpa using hp1) f g hf hg hconv
  have hpow := hnorm.pow p
  simpa only [← integral_norm_pow_eq_lpNorm_pow p hp _ hg.aestronglyMeasurable,
    ← integral_norm_pow_eq_lpNorm_pow p hp _ (hf _).aestronglyMeasurable] using hpow

/-- The `L⁴` requirement stored in a certified weak field is an actual
`MemLp` assertion, allowing Mathlib's norm and Hölder inequalities. -/
theorem WeakH1L4BallField.memLp_four {n : ℕ} {R : ℝ}
    (U : WeakH1L4BallField n R) :
    MemLp U.u 4 (weakBallMeasure n R) := by
  have h := (integrable_norm_rpow_iff U.uMeas
    (p := (4 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp
  apply h
  simpa using U.uL4

/-- The `H¹` part of a certified weak field gives its `L²` map bound. -/
theorem WeakH1L4BallField.memLp_two {n : ℕ} {R : ℝ}
    (U : WeakH1L4BallField n R) :
    MemLp U.u 2 (weakBallMeasure n R) := by
  have h := (integrable_norm_rpow_iff U.uMeas
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp
  apply h
  simpa using U.uL2

/-- Each column of the weak gradient is square integrable. -/
theorem WeakH1L4BallField.grad_column_memLp_two
    {n : ℕ} {R : ℝ} (U : WeakH1L4BallField n R) (i : Fin n) :
    MemLp (fun x => U.grad x (EuclideanSpace.single i (1 : ℝ)))
      2 (weakBallMeasure n R) := by
  let e : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
  have hMeas : AEStronglyMeasurable (fun x => U.grad x e)
      (weakBallMeasure n R) := U.gradMeas.apply_continuousLinearMap e
  have hSqMeas : AEStronglyMeasurable (fun x => ‖U.grad x e‖ ^ 2)
      (weakBallMeasure n R) := hMeas.norm.pow 2
  have hSqInt : Integrable (fun x => ‖U.grad x e‖ ^ 2)
      (weakBallMeasure n R) := by
    apply Integrable.mono_nonneg U.gradL2 hSqMeas
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    apply Filter.Eventually.of_forall
    intro x
    change ‖U.grad x e‖ ^ 2 ≤
      ∑ j : Fin n, ‖U.grad x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (‖U.grad x (EuclideanSpace.single j (1 : ℝ))‖))
      (Finset.mem_univ i)
  exact (memLp_two_iff_integrable_sq_norm hMeas).2 hSqInt

/-- Integrability of the constant term on a ball, needed to expand the
double-well potential without invoking a totalized integral. -/
private theorem ball_one_integrable (n : ℕ) (R : ℝ) :
    Integrable (fun _ : GLEuclidean n => (1 : ℝ))
      (weakBallMeasure n R) := by
  change IntegrableOn (fun _ : GLEuclidean n => (1 : ℝ))
    (Metric.ball (0 : GLEuclidean n) R) volume
  exact integrableOn_const measure_ball_ne_top

/-- Algebraic decomposition of the genuine weak energy into finite
`L²` gradient, `L²` map, and `L⁴` map moments. -/
theorem WeakH1L4BallField.energy_moment_formula
    {n : ℕ} {R : ℝ} (U : WeakH1L4BallField n R) :
    U.energy =
      (∑ i : Fin n,
        ∫ x, ‖U.grad x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
          ∂(weakBallMeasure n R)) / 2 +
      ((∫ _ : GLEuclidean n, (1 : ℝ) ∂(weakBallMeasure n R)) -
        2 * (∫ x, ‖U.u x‖ ^ 2 ∂(weakBallMeasure n R)) +
        (∫ x, ‖U.u x‖ ^ 4 ∂(weakBallMeasure n R))) / 4 := by
  let μ := weakBallMeasure n R
  have hgi (i : Fin n) :
      Integrable (fun x =>
        ‖U.grad x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) μ :=
    (U.grad_column_memLp_two i).integrable_norm_pow (by norm_num)
  have hgrad :
      (∫ x, weakGradientSq n U.grad x ∂μ) =
        ∑ i : Fin n,
          ∫ x, ‖U.grad x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ∂μ := by
    simp only [weakGradientSq]
    exact integral_finset_sum Finset.univ (fun i _ => hgi i)
  have hpotInt : Integrable
      (fun x => 1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4) μ :=
    ((ball_one_integrable n R).sub (U.uL2.const_mul 2)).add U.uL4
  have hpot :
      (∫ x, 1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4 ∂μ) =
      (∫ _ : GLEuclidean n, (1 : ℝ) ∂μ) -
        2 * (∫ x, ‖U.u x‖ ^ 2 ∂μ) +
        (∫ x, ‖U.u x‖ ^ 4 ∂μ) := by
    have hadd := integral_add
      ((ball_one_integrable n R).sub (U.uL2.const_mul 2)) U.uL4
    have hsub := integral_sub (ball_one_integrable n R) (U.uL2.const_mul 2)
    calc
      (∫ x, 1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4 ∂μ) =
          (∫ x, 1 - 2 * ‖U.u x‖ ^ 2 ∂μ) +
          (∫ x, ‖U.u x‖ ^ 4 ∂μ) := by
        simpa only [Pi.add_apply, Pi.sub_apply] using hadd
      _ = ((∫ _ : GLEuclidean n, (1 : ℝ) ∂μ) -
          (∫ x, 2 * ‖U.u x‖ ^ 2 ∂μ)) +
          (∫ x, ‖U.u x‖ ^ 4 ∂μ) := by
        rw [show (∫ x, 1 - 2 * ‖U.u x‖ ^ 2 ∂μ) =
          (∫ _ : GLEuclidean n, (1 : ℝ) ∂μ) -
          (∫ x, 2 * ‖U.u x‖ ^ 2 ∂μ) by
            simpa only [Pi.sub_apply] using hsub]
      _ = _ := by rw [integral_const_mul]
  change weakBallEnergy n R U.u U.grad = _
  unfold weakBallEnergy
  have hdensity (x : GLEuclidean n) :
      weakGradientSq n U.grad x / 2 + (1 - ‖U.u x‖ ^ 2) ^ 2 / 4 =
      weakGradientSq n U.grad x / 2 +
        (1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4) / 4 := by ring
  simp_rw [hdensity]
  rw [integral_add (U.gradL2.div_const 2) (hpotInt.div_const 4),
    integral_div, integral_div, hgrad, hpot]

/-- Strong convergence of all gradient columns in `L²`, of the map in
`L²`, and of the map in `L⁴` forces convergence of the genuine weak
energy.  A subsequent finite-measure lemma reduces the two map hypotheses
to the `L⁴` one used in the manuscript. -/
theorem weakBallEnergy_tendsto_of_strongL2L4
    {n : ℕ} {R : ℝ} {ι : Type*} {l : Filter ι}
    (V : ι → WeakH1L4BallField n R) (U : WeakH1L4BallField n R)
    (hu2 : Tendsto
      (fun j => lpNorm ((V j).u - U.u) 2 (weakBallMeasure n R))
      l (nhds 0))
    (hu4 : Tendsto
      (fun j => lpNorm ((V j).u - U.u) 4 (weakBallMeasure n R))
      l (nhds 0))
    (hgrad : ∀ i : Fin n, Tendsto
      (fun j => lpNorm
        (fun x => (V j).grad x (EuclideanSpace.single i (1 : ℝ)) -
          U.grad x (EuclideanSpace.single i (1 : ℝ)))
        2 (weakBallMeasure n R)) l (nhds 0)) :
    Tendsto (fun j => (V j).energy) l (nhds U.energy) := by
  let μ := weakBallMeasure n R
  have hu2mom : Tendsto
      (fun j => ∫ x, ‖(V j).u x‖ ^ 2 ∂μ) l
      (nhds (∫ x, ‖U.u x‖ ^ 2 ∂μ)) := by
    apply integral_norm_pow_tendsto_of_strongLp 2 (by norm_num) (by norm_num)
      (fun j => (V j).u) U.u
      (fun j => (V j).memLp_two) U.memLp_two
    simpa [Pi.sub_apply] using hu2
  have hu4mom : Tendsto
      (fun j => ∫ x, ‖(V j).u x‖ ^ 4 ∂μ) l
      (nhds (∫ x, ‖U.u x‖ ^ 4 ∂μ)) := by
    apply integral_norm_pow_tendsto_of_strongLp 4 (by norm_num) (by norm_num)
      (fun j => (V j).u) U.u
      (fun j => (V j).memLp_four) U.memLp_four
    simpa [Pi.sub_apply] using hu4
  have hgimom (i : Fin n) : Tendsto
      (fun j => ∫ x,
        ‖(V j).grad x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ∂μ) l
      (nhds (∫ x,
        ‖U.grad x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ∂μ)) := by
    apply integral_norm_pow_tendsto_of_strongLp 2 (by norm_num) (by norm_num)
      (fun j x => (V j).grad x (EuclideanSpace.single i (1 : ℝ)))
      (fun x => U.grad x (EuclideanSpace.single i (1 : ℝ)))
      (fun j => (V j).grad_column_memLp_two i) (U.grad_column_memLp_two i)
    simpa [Pi.sub_apply] using hgrad i
  have hgradmom : Tendsto
      (fun j => ∑ i : Fin n,
        ∫ x, ‖(V j).grad x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ∂μ) l
      (nhds (∑ i : Fin n,
        ∫ x, ‖U.grad x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ∂μ)) := by
    exact tendsto_finset_sum Finset.univ (fun i _ => hgimom i)
  have hpot : Tendsto
      (fun j => (∫ _ : GLEuclidean n, (1 : ℝ) ∂μ) -
        2 * (∫ x, ‖(V j).u x‖ ^ 2 ∂μ) +
        (∫ x, ‖(V j).u x‖ ^ 4 ∂μ)) l
      (nhds ((∫ _ : GLEuclidean n, (1 : ℝ) ∂μ) -
        2 * (∫ x, ‖U.u x‖ ^ 2 ∂μ) +
        (∫ x, ‖U.u x‖ ^ 4 ∂μ))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hu2mom)).add hu4mom
  have hsum := (hgradmom.div_const 2).add (hpot.div_const 4)
  simpa only [WeakH1L4BallField.energy_moment_formula] using hsum

/-- On finite-measure domains, the `L⁴` norm controls the `L²` norm. -/
theorem lpNorm_two_le_four_mul_mass
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ]
    (f : α → E) (hf : MemLp f 4 μ) :
    lpNorm f 2 μ ≤
      lpNorm f 4 μ * (μ Set.univ).toReal ^ (1 / 4 : ℝ) := by
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := (2 : ℝ≥0∞)) (q := (4 : ℝ≥0∞))
    (by norm_num) hf.aestronglyMeasurable
  have hmass : (μ Set.univ) ^ (1 / 2 - 1 / 4 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top hmass) hcmp
  simpa only [toReal_eLpNorm hf.aestronglyMeasurable,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    show (1 / 2 - 1 / 4 : ℝ) = 1 / 4 by norm_num] using hreal

/-- Strong `L⁴` convergence implies strong `L²` convergence on finite
measure domains. -/
theorem tendsto_lpNorm_two_of_strongL4
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {ι : Type*} {l : Filter ι}
    (f : ι → α → E) (g : α → E)
    (hf : ∀ j, MemLp (f j) 4 μ) (hg : MemLp g 4 μ)
    (hconv : Tendsto (fun j => lpNorm (f j - g) 4 μ) l (nhds 0)) :
    Tendsto (fun j => lpNorm (f j - g) 2 μ) l (nhds 0) := by
  have hbound (j : ι) :
      lpNorm (f j - g) 2 μ ≤
        lpNorm (f j - g) 4 μ *
          (μ Set.univ).toReal ^ (1 / 4 : ℝ) :=
    lpNorm_two_le_four_mul_mass _ ((hf j).sub hg)
  have hscaled : Tendsto
      (fun j => lpNorm (f j - g) 4 μ *
        (μ Set.univ).toReal ^ (1 / 4 : ℝ)) l (nhds 0) := by
    simpa using (hconv.mul_const ((μ Set.univ).toReal ^ (1 / 4 : ℝ)))
  exact squeeze_zero (fun j => lpNorm_nonneg) hbound hscaled

/-- The precise algebraic/measure-theoretic closure step for the paper's
`H¹∩L⁴` energy: strong `L²` convergence of each weak-gradient column and
strong `L⁴` convergence of the maps imply convergence of their energies.
No approximation sequence is manufactured here. -/
theorem weakBallEnergy_tendsto_of_strongH1L4
    {n : ℕ} {R : ℝ} {ι : Type*} {l : Filter ι}
    (V : ι → WeakH1L4BallField n R) (U : WeakH1L4BallField n R)
    (hu4 : Tendsto
      (fun j => lpNorm ((V j).u - U.u) 4 (weakBallMeasure n R))
      l (nhds 0))
    (hgrad : ∀ i : Fin n, Tendsto
      (fun j => lpNorm
        (fun x => (V j).grad x (EuclideanSpace.single i (1 : ℝ)) -
          U.grad x (EuclideanSpace.single i (1 : ℝ)))
        2 (weakBallMeasure n R)) l (nhds 0)) :
    Tendsto (fun j => (V j).energy) l (nhds U.energy) := by
  letI : IsFiniteMeasure (weakBallMeasure n R) := by
    change IsFiniteMeasure
      (volume.restrict (Metric.ball (0 : GLEuclidean n) R))
    exact isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hu2 := tendsto_lpNorm_two_of_strongL4
    (fun j => (V j).u) U.u
    (fun j => (V j).memLp_four) U.memLp_four
    (by simpa [Pi.sub_apply] using hu4)
  apply weakBallEnergy_tendsto_of_strongL2L4 V U
    (by simpa [Pi.sub_apply] using hu2) hu4 hgrad

end

end BrezisOP6
