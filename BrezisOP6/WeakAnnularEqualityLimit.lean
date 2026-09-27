import BrezisOP6.WeakStrongClosureMain
import BrezisOP6.EnergyAnnulusIntegral

/-!
# Equality in the weak class from smooth annular stability

The main argument here is a limit theorem.  Its quantitative hypothesis is
the *smooth* stability inequality on each annulus; it does not assume that a
weak equality case is smooth.  Strong `L⁴` convergence supplies strong `L²`
convergence, and the fixed-energy equality makes the annular squared distance
vanish.  A countable family of annuli then exhausts the ball up to its null
centre.
-/

namespace BrezisOP6

open MeasureTheory Filter Metric Set
open scoped Topology

noncomputable section

/-- A quantitative bound for smooth approximants on one measurable set,
together with strong `L²` convergence, forces the limit to equal the base on
that set when the energy gap vanishes. -/
theorem ae_eq_on_set_of_strongL2_and_gap_stability
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s)
    (V : ℕ → α → E) (U base : α → E)
    (hV : ∀ j, MemLp (V j) 2 μ)
    (hU : MemLp U 2 μ) (hBase : MemLp base 2 μ)
    (hStrong : Tendsto (fun j => lpNorm (V j - U) 2 μ) atTop (𝓝 0))
    (gap : ℕ → ℝ) (hGap : Tendsto gap atTop (𝓝 0))
    (hStable : ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (∫ x in s, ‖V j x - base x‖ ^ 2 ∂μ) ≤ C * gap j) :
    U =ᵐ[μ.restrict s] base := by
  obtain ⟨C, hC, hStable⟩ := hStable
  have hDiffGlobal (j : ℕ) : Integrable
      (fun x => ‖V j x - U x‖ ^ 2) μ := by
    simpa only [Pi.sub_apply] using
      ((hV j).sub hU).integrable_norm_pow (by norm_num)
  have hDiffBase (j : ℕ) : Integrable
      (fun x => ‖V j x - base x‖ ^ 2) μ := by
    simpa only [Pi.sub_apply] using
      ((hV j).sub hBase).integrable_norm_pow (by norm_num)
  have hLimitDiff : Tendsto
      (fun j => ∫ x, ‖V j x - U x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hSubtractZero (j : ℕ) :
        (fun x => V j x - U x) - (fun _ => (0 : E)) = V j - U := by
      funext x
      simp [Pi.sub_apply]
    have h := integral_norm_pow_tendsto_of_strongLp
      (μ := μ) (l := atTop)
      2 (by norm_num) (by norm_num)
      (fun j x => V j x - U x) (fun _ => (0 : E))
      (fun j => (hV j).sub hU) (by simpa using (memLp_zero : MemLp (fun _ : α => (0 : E)) 2 μ))
      (by simpa only [hSubtractZero] using hStrong)
    simpa using h
  have hBaseInt : Integrable
      (fun x => ‖U x - base x‖ ^ 2) (μ.restrict s) := by
    have h := (hU.sub hBase).integrable_norm_pow (by norm_num)
    simpa only [Pi.sub_apply] using h.restrict
  have hBaseNonneg : 0 ≤ ∫ x in s, ‖U x - base x‖ ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have hUpperLimit : Tendsto
      (fun j => 2 * (∫ x, ‖V j x - U x‖ ^ 2 ∂μ) +
        2 * (C * gap j)) atTop (𝓝 0) := by
    convert (hLimitDiff.const_mul 2).add ((hGap.const_mul C).const_mul 2) using 1 <;>
      simp [mul_assoc]
  have hUpper (j : ℕ) :
      (∫ x in s, ‖U x - base x‖ ^ 2 ∂μ) ≤
        2 * (∫ x, ‖V j x - U x‖ ^ 2 ∂μ) + 2 * (C * gap j) := by
    have hG : Integrable (fun x => ‖V j x - U x‖ ^ 2) (μ.restrict s) :=
      (hDiffGlobal j).restrict
    have hH : Integrable (fun x => ‖V j x - base x‖ ^ 2) (μ.restrict s) :=
      (hDiffBase j).restrict
    have hUpperInt : Integrable
        (fun x => 2 * ‖V j x - U x‖ ^ 2 +
          2 * ‖V j x - base x‖ ^ 2) (μ.restrict s) :=
      (hG.const_mul 2).add (hH.const_mul 2)
    have hPoint (x : α) :
        ‖U x - base x‖ ^ 2 ≤
          2 * ‖V j x - U x‖ ^ 2 +
            2 * ‖V j x - base x‖ ^ 2 := by
      have hvec : U x - base x = (U x - V j x) + (V j x - base x) := by
        abel
      have htri : ‖U x - base x‖ ≤
          ‖V j x - U x‖ + ‖V j x - base x‖ := by
        rw [hvec]
        simpa only [norm_sub_rev] using
          (norm_add_le (U x - V j x) (V j x - base x))
      nlinarith [sq_nonneg (‖V j x - U x‖ - ‖V j x - base x‖),
        norm_nonneg (U x - base x), norm_nonneg (V j x - U x),
        norm_nonneg (V j x - base x)]
    have hIntegralPoint :
        (∫ x in s, ‖U x - base x‖ ^ 2 ∂μ) ≤
          ∫ x in s, (2 * ‖V j x - U x‖ ^ 2 +
            2 * ‖V j x - base x‖ ^ 2) ∂μ :=
      setIntegral_mono_on hBaseInt hUpperInt hs (fun x _ => hPoint x)
    have hUpperEq :
        (∫ x in s, (2 * ‖V j x - U x‖ ^ 2 +
            2 * ‖V j x - base x‖ ^ 2) ∂μ) =
          2 * (∫ x in s, ‖V j x - U x‖ ^ 2 ∂μ) +
            2 * (∫ x in s, ‖V j x - base x‖ ^ 2 ∂μ) := by
      rw [integral_add (hG.const_mul 2) (hH.const_mul 2),
        integral_const_mul, integral_const_mul]
    have hGle : (∫ x in s, ‖V j x - U x‖ ^ 2 ∂μ) ≤
        ∫ x, ‖V j x - U x‖ ^ 2 ∂μ :=
      setIntegral_le_integral (hDiffGlobal j)
        (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    calc
      _ ≤ ∫ x in s, (2 * ‖V j x - U x‖ ^ 2 +
            2 * ‖V j x - base x‖ ^ 2) ∂μ := hIntegralPoint
      _ = 2 * (∫ x in s, ‖V j x - U x‖ ^ 2 ∂μ) +
            2 * (∫ x in s, ‖V j x - base x‖ ^ 2 ∂μ) := hUpperEq
      _ ≤ 2 * (∫ x, ‖V j x - U x‖ ^ 2 ∂μ) +
            2 * (C * gap j) := by linarith [hGle, hStable j]
  have hZero : (∫ x in s, ‖U x - base x‖ ^ 2 ∂μ) = 0 :=
    le_antisymm (ge_of_tendsto hUpperLimit
      (Eventually.of_forall hUpper)) hBaseNonneg
  have hNormZero :
      (fun x => ‖U x - base x‖ ^ 2) =ᵐ[μ.restrict s]
        (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg (‖U x - base x‖)) hBaseInt).mp hZero
  filter_upwards [hNormZero] with x hx
  have hnorm : ‖U x - base x‖ = 0 := by
    have hnonneg := norm_nonneg (U x - base x)
    nlinarith [hx]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Annular almost-everywhere equality exhausts a ball up to its centre.
The centre is explicitly assumed null, as it is for Euclidean volume in
positive dimension.  No regularity of either field enters this argument. -/
theorem ae_eq_of_annular_ae_eq
    (n : ℕ) (R : ℝ) (μ : Measure (GLEuclidean n))
    (U base : GLEuclidean n → GLEuclidean n)
    (hBall : ∀ᵐ x ∂μ, x ∈ Metric.ball (0 : GLEuclidean n) R)
    (hNeZero : ∀ᵐ x ∂μ, x ≠ 0)
    (hAnnulus : ∀ δ ρ : ℝ, 0 < δ → δ < ρ → ρ < R →
      U =ᵐ[μ.restrict (energyPositiveAnnulus n δ ρ)] base) :
    U =ᵐ[μ] base := by
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let ρ : ℕ → ℝ := fun k => R - δ k
  have hAll : ∀ᵐ x ∂μ, ∀ k : ℕ,
      (0 < δ k ∧ δ k < ρ k ∧ ρ k < R) →
        (x ∈ energyPositiveAnnulus n (δ k) (ρ k) → U x = base x) := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : 0 < δ k ∧ δ k < ρ k ∧ ρ k < R
    · exact ((ae_restrict_iff'
          (measurableSet_energyPositiveAnnulus n (δ k) (ρ k))).mp
          (hAnnulus (δ k) (ρ k) hk.1 hk.2.1 hk.2.2)).mono
          (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hk h).elim)
  filter_upwards [hAll, hBall, hNeZero] with x hx hxBall hxNe
  have hxPos : 0 < ‖x‖ := norm_pos_iff.mpr hxNe
  have hxR : ‖x‖ < R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxBall
  obtain ⟨k, hk⟩ :=
    exists_nat_one_div_lt (lt_min hxPos (sub_pos.mpr hxR))
  have hδPos : 0 < δ k := by
    dsimp [δ]
    positivity
  have hδNorm : δ k < ‖x‖ :=
    lt_of_lt_of_le (by simpa [δ] using hk) (min_le_left _ _)
  have hδMargin : δ k < R - ‖x‖ :=
    lt_of_lt_of_le (by simpa [δ] using hk) (min_le_right _ _)
  have hδρ : δ k < ρ k := by
    dsimp [ρ]
    linarith
  have hρR : ρ k < R := by
    dsimp [ρ]
    linarith
  have hxAnnulus : x ∈ energyPositiveAnnulus n (δ k) (ρ k) := by
    change ‖x‖ ∈ Ioc (δ k) (ρ k)
    constructor
    · exact hδNorm
    · dsimp [ρ]
      linarith
  exact hx k ⟨hδPos, hδρ, hρR⟩ hxAnnulus

/-- The abstract equality endpoint needed by the paper: the only
nontrivial extra premise is a *uniform smooth annular stability estimate*.
This replaces an equality-case regularity assumption by a quantitative
limit argument. -/
theorem weak_ae_eq_of_strong_closure_and_smooth_annular_stability
    (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (base U : WeakH1L4BallField (m + 3) R)
    (hClosure : WeakSmoothFixedTraceStrongClosure m R f U)
    (hStable : ∀ δ ρ : ℝ, 0 < δ → δ < ρ → ρ < R →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ V : WeakH1L4BallField (m + 3) R,
          SmoothBallCompetitor m R f V.u →
          V.grad = fderiv ℝ V.u →
          (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
              ‖V.u x - base.u x‖ ^ 2
                ∂(weakBallMeasure (m + 3) R)) ≤
            C * (V.energy - base.energy))
    (hEq : U.energy = base.energy) :
    U.u =ᵐ[weakBallMeasure (m + 3) R] base.u := by
  obtain ⟨V, hSmooth, hu4, hgrad⟩ := hClosure
  let μ := weakBallMeasure (m + 3) R
  letI : IsFiniteMeasure μ := by
    change IsFiniteMeasure
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R))
    exact isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hu2 : Tendsto
      (fun j => lpNorm ((V j).u - U.u) 2 μ) atTop (𝓝 0) := by
    exact tendsto_lpNorm_two_of_strongL4
      (fun j => (V j).u) U.u
      (fun j => (V j).memLp_four) U.memLp_four
      (by simpa [μ, Pi.sub_apply] using hu4)
  have hEnergy : Tendsto (fun j => (V j).energy) atTop
      (𝓝 U.energy) := weakBallEnergy_tendsto_of_strongH1L4 V U hu4 hgrad
  have hGap : Tendsto (fun j => (V j).energy - base.energy) atTop
      (𝓝 0) := by
    convert hEnergy.sub_const base.energy using 1 <;> simp [hEq]
  have hAnnulus (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ < ρ)
      (hρR : ρ < R) :
      U.u =ᵐ[μ.restrict (energyPositiveAnnulus (m + 3) δ ρ)] base.u := by
    obtain ⟨C, hC, hSC⟩ := hStable δ ρ hδ hδρ hρR
    apply ae_eq_on_set_of_strongL2_and_gap_stability
      (energyPositiveAnnulus (m + 3) δ ρ)
      (measurableSet_energyPositiveAnnulus (m + 3) δ ρ)
      (fun j => (V j).u) U.u base.u
      (fun j => (V j).memLp_two) U.memLp_two base.memLp_two
      (by simpa [μ, Pi.sub_apply] using hu2)
      (fun j => (V j).energy - base.energy) hGap
    exact ⟨C, hC, fun j => hSC (V j) (hSmooth j).1 (hSmooth j).2⟩
  apply ae_eq_of_annular_ae_eq (m + 3) R μ U.u base.u
  · change ∀ᵐ x ∂(volume.restrict
        (Metric.ball (0 : GLEuclidean (m + 3)) R)),
        x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R
    exact ae_restrict_mem Metric.isOpen_ball.measurableSet
  · have hNull : ∀ᵐ x : GLEuclidean (m + 3) ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff] using
        (measure_singleton (0 : GLEuclidean (m + 3)) :
          volume ({0} : Set (GLEuclidean (m + 3))) = 0)
    exact ae_restrict_of_ae hNull
  · exact hAnnulus

/-- The paper's weak fixed-trace minimum and its equality conclusion, once
the actual strong fixed-trace density and the smooth quantitative annular
estimate have been established.  The comparison itself uses the previously
proved smooth minimum; the equality passage needs no regularity of a weak
minimizer. -/
theorem weak_minimum_and_ae_equality_of_strong_closure_and_annular_stability
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (base : WeakH1L4BallField (m + 3) R)
    (hBaseEnergy : base.energy =
      euclideanBallEnergy (m + 3) R
        (radialVortex (m + 3) p.f))
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor base)
    (hClosure : WeakSmoothFixedTraceStrongClosure m R p.f U.field)
    (hStable : ∀ δ ρ : ℝ, 0 < δ → δ < ρ → ρ < R →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ V : WeakH1L4BallField (m + 3) R,
          SmoothBallCompetitor m R p.f V.u →
          V.grad = fderiv ℝ V.u →
          (∫ x in energyPositiveAnnulus (m + 3) δ ρ,
              ‖V.u x - base.u x‖ ^ 2
                ∂(weakBallMeasure (m + 3) R)) ≤
            C * (V.energy - base.energy)) :
    base.energy ≤ U.field.energy ∧
      (U.field.energy = base.energy →
        U.field.u =ᵐ[weakBallMeasure (m + 3) R] base.u) := by
  have hClosureCopy := hClosure
  obtain ⟨V, hSmooth, hu4, hgrad⟩ := hClosure
  have hEnergy : Tendsto (fun j => (V j).energy) atTop
      (𝓝 U.field.energy) :=
    weakBallEnergy_tendsto_of_strongH1L4 V U.field hu4 hgrad
  constructor
  · apply ge_of_tendsto hEnergy
    exact Eventually.of_forall (fun j => by
      have hV : (V j).energy =
          euclideanBallEnergy (m + 3) R (V j).u := by
        rw [WeakH1L4BallField.energy, (hSmooth j).2,
          weakBallEnergy_classical_gradient]
      rw [hBaseEnergy, hV]
      exact (physical_smooth_ball_minimum_and_ae_equality
        m R p hPublished hLocal (V j).u (hSmooth j).1).1)
  · intro hEq
    exact weak_ae_eq_of_strong_closure_and_smooth_annular_stability
      m R p.f base U.field hClosureCopy hStable hEq

end

end BrezisOP6
