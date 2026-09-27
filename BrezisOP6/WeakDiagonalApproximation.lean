import BrezisOP6.WeakJointInteriorApproximation
import BrezisOP6.WeakDilationStrongLp

/-!
# Toward a single fixed-trace approximation sequence

The distributional zero extension has strong `L⁴` dilation continuity,
and each certified weak-gradient component has strong `L²` continuity with
the correct chain-rule coefficient. The one-shot interior mollifiers of
`WeakJointInteriorApproximation` can therefore be diagonalized against a
common inward scale.
-/

namespace BrezisOP6

open MeasureTheory Filter Metric
open scoped ENNReal Topology

noncomputable section

/-- Function-coordinate `L⁴` convergence of the actual zero extension
under the standard inward scale. -/
theorem WeakFixedTraceCompetitor.inward_zeroTrace_component_L4_tendsto
    {n : ℕ} [NeZero n] {R : ℝ}
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) (j : Fin n) :
    Tendsto (fun k => eLpNorm
      (fun x =>
        (inwardDilation n (standardInwardScale k)
          (zeroExtendedDifference n R U.field.u base.u) x) j -
          (zeroExtendedDifference n R U.field.u base.u x) j)
      4 volume) atTop (nhds 0) := by
  simpa only [inwardDilation] using
    (eLpNorm_inward_sub_tendsto_of_memLp
      (U.zeroTrace.component_memLp_four j) (by norm_num) (by norm_num)
      standardInwardScale standardInwardScale_pos standardInwardScale_lt_one
      standardInwardScale_tendsto_one)

/-- The same statement in `L²`, useful for explicit `H¹` closure. -/
theorem WeakFixedTraceCompetitor.inward_zeroTrace_component_L2_tendsto
    {n : ℕ} [NeZero n] {R : ℝ}
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) (j : Fin n) :
    Tendsto (fun k => eLpNorm
      (fun x =>
        (inwardDilation n (standardInwardScale k)
          (zeroExtendedDifference n R U.field.u base.u) x) j -
          (zeroExtendedDifference n R U.field.u base.u x) j)
      2 volume) atTop (nhds 0) := by
  simpa only [inwardDilation] using
    (eLpNorm_inward_sub_tendsto_of_memLp
      (U.zeroTrace.component_memLp_two j) (by norm_num) (by norm_num)
      standardInwardScale standardInwardScale_pos standardInwardScale_lt_one
      standardInwardScale_tendsto_one)

/-- Each weak-gradient coordinate converges in `L²` after inward
dilation with the genuine `a⁻¹` derivative factor. -/
theorem WeakFixedTraceCompetitor.inward_zeroTrace_gradient_component_L2_tendsto
    {n : ℕ} [NeZero n] {R : ℝ}
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) (j i : Fin n) :
    Tendsto (fun k => lpNorm
      (fun x =>
        (inwardGradient n (standardInwardScale k)
          (zeroExtendedGradientDifference n R U.field.grad base.grad)
          x (EuclideanSpace.single i (1 : ℝ))) j -
          (zeroExtendedGradientDifference n R U.field.grad base.grad
            x (EuclideanSpace.single i (1 : ℝ))) j)
      2 volume) atTop (nhds 0) := by
  simpa only [inwardGradient, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Pi.smul_apply] using
    (lpNorm_inwardGradient_sub_tendsto_of_memLp
      (U.zeroTrace.gradient_component_memLp_two j i)
      (by norm_num) (by norm_num)
      standardInwardScale standardInwardScale_pos standardInwardScale_lt_one
      standardInwardScale_tendsto_one)

/-- Choose one mollification index for every inward scale, uniformly over
all finitely many output coordinates and derivative directions. The error
at scale `k` is at most `1/(k+1)` in all three required norms. -/
theorem WeakFixedTraceCompetitor.exists_moving_coordinate_mollifiers
    {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) :
    ∃ φ : Fin n → ℕ → GLEuclidean n → ℝ,
      (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (φ j k)) ∧
      (∀ j k, HasCompactSupport (φ j k)) ∧
      (∀ j k, tsupport (φ j k) ⊆ Metric.ball (0 : GLEuclidean n) R) ∧
      (∀ j k, eLpNorm
        (fun x => φ j k x -
          (inwardDilation n (standardInwardScale k)
            (zeroExtendedDifference n R U.field.u base.u) x) j)
        2 volume ≤ ENNReal.ofReal (((k : ℝ) + 1)⁻¹)) ∧
      (∀ j k, eLpNorm
        (fun x => φ j k x -
          (inwardDilation n (standardInwardScale k)
            (zeroExtendedDifference n R U.field.u base.u) x) j)
        4 volume ≤ ENNReal.ofReal (((k : ℝ) + 1)⁻¹)) ∧
      (∀ j i k, eLpNorm
        (fun x => (fderiv ℝ (φ j k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            (inwardGradient n (standardInwardScale k)
              (zeroExtendedGradientDifference n R U.field.grad base.grad)
              x (EuclideanSpace.single i (1 : ℝ))) j)
        2 volume ≤ ENNReal.ofReal (((k : ℝ) + 1)⁻¹)) := by
  classical
  let ε (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have happrox (k : ℕ) :=
    U.inward_all_components_joint_approx hR base
      (standardInwardScale k)
      (standardInwardScale_pos k) (standardInwardScale_lt_one k)
  choose ψ hSmooth hCompact hSupport hTwo hGrad hFour using happrox
  have hsmallTwo (k : ℕ) : ∀ᶠ q in atTop, ∀ j : Fin n,
      eLpNorm (fun x => ψ k j q x -
        (inwardDilation n (standardInwardScale k)
          (zeroExtendedDifference n R U.field.u base.u) x) j)
        2 volume ≤ ENNReal.ofReal (ε k) := by
    exact Filter.eventually_all.2 (fun j =>
      ENNReal.tendsto_nhds_zero.1 (hTwo k j) _
        (ENNReal.ofReal_pos.mpr (hεpos k)))
  have hsmallFour (k : ℕ) : ∀ᶠ q in atTop, ∀ j : Fin n,
      eLpNorm (fun x => ψ k j q x -
        (inwardDilation n (standardInwardScale k)
          (zeroExtendedDifference n R U.field.u base.u) x) j)
        4 volume ≤ ENNReal.ofReal (ε k) := by
    exact Filter.eventually_all.2 (fun j =>
      ENNReal.tendsto_nhds_zero.1 (hFour k j) _
        (ENNReal.ofReal_pos.mpr (hεpos k)))
  have hsmallGrad (k : ℕ) : ∀ᶠ q in atTop, ∀ j i : Fin n,
      eLpNorm (fun x => (fderiv ℝ (ψ k j q) x)
        (EuclideanSpace.single i (1 : ℝ)) -
          (inwardGradient n (standardInwardScale k)
            (zeroExtendedGradientDifference n R U.field.grad base.grad)
            x (EuclideanSpace.single i (1 : ℝ))) j)
        2 volume ≤ ENNReal.ofReal (ε k) := by
    exact Filter.eventually_all.2 (fun j =>
      Filter.eventually_all.2 (fun i =>
        ENNReal.tendsto_nhds_zero.1 (hGrad k j i) _
          (ENNReal.ofReal_pos.mpr (hεpos k))))
  have hNexists (k : ℕ) : ∃ N : ℕ, ∀ q ≥ N,
      (∀ j : Fin n,
        eLpNorm (fun x => ψ k j q x -
          (inwardDilation n (standardInwardScale k)
            (zeroExtendedDifference n R U.field.u base.u) x) j)
          2 volume ≤ ENNReal.ofReal (ε k)) ∧
      (∀ j : Fin n,
        eLpNorm (fun x => ψ k j q x -
          (inwardDilation n (standardInwardScale k)
            (zeroExtendedDifference n R U.field.u base.u) x) j)
          4 volume ≤ ENNReal.ofReal (ε k)) ∧
      (∀ j i : Fin n,
        eLpNorm (fun x => (fderiv ℝ (ψ k j q) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            (inwardGradient n (standardInwardScale k)
              (zeroExtendedGradientDifference n R U.field.grad base.grad)
              x (EuclideanSpace.single i (1 : ℝ))) j)
          2 volume ≤ ENNReal.ofReal (ε k)) := by
    apply Filter.eventually_atTop.1
    filter_upwards [hsmallTwo k, hsmallFour k, hsmallGrad k]
      with q h2 h4 hg
    exact ⟨h2, h4, hg⟩
  choose N hN using hNexists
  let φ (j : Fin n) (k : ℕ) := ψ k j (N k)
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j k
    exact hSmooth k j (N k)
  · intro j k
    exact hCompact k j (N k)
  · intro j k
    exact hSupport k j (N k)
  · intro j k
    simpa [φ, ε] using (hN k (N k) le_rfl).1 j
  · intro j k
    simpa [φ, ε] using (hN k (N k) le_rfl).2.1 j
  · intro j i k
    simpa [φ, ε] using (hN k (N k) le_rfl).2.2 j i

/-- One sequence of interior smooth mollifiers converges to the original
zero extension simultaneously in every value `L⁴` and weak-gradient `L²`
coordinate. Both limits refer to the undilated field. -/
theorem WeakFixedTraceCompetitor.exists_coordinate_joint_approx_of_zeroTrace
    {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (base : WeakH1L4BallField n R)
    (U : WeakFixedTraceCompetitor base) :
    ∃ φ : Fin n → ℕ → GLEuclidean n → ℝ,
      (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (φ j k)) ∧
      (∀ j k, HasCompactSupport (φ j k)) ∧
      (∀ j k, tsupport (φ j k) ⊆ Metric.ball (0 : GLEuclidean n) R) ∧
      (∀ j, Tendsto (fun k => eLpNorm
        (fun x => φ j k x -
          (zeroExtendedDifference n R U.field.u base.u x) j)
        4 volume) atTop (nhds 0)) ∧
      (∀ j i, Tendsto (fun k => lpNorm
        (fun x => (fderiv ℝ (φ j k) x)
          (EuclideanSpace.single i (1 : ℝ)) -
            (zeroExtendedGradientDifference n R U.field.grad base.grad
              x (EuclideanSpace.single i (1 : ℝ))) j)
        2 volume) atTop (nhds 0)) := by
  obtain ⟨φ, hSmooth, hCompact, hSupport, _hTwo, hFour, hGrad⟩ :=
    U.exists_moving_coordinate_mollifiers hR base
  let w := zeroExtendedDifference n R U.field.u base.u
  have hε : Tendsto
      (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1)⁻¹))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹)
        atTop (nhds (0 : ℝ)) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  have hWcoord (j : Fin n) :
      AEStronglyMeasurable (fun x => (w x) j) volume :=
    (EuclideanSpace.proj j).continuous.aestronglyMeasurable.comp_aemeasurable
      U.zeroTrace.1.aemeasurable
  have hWaCoord (j : Fin n) (k : ℕ) :
      AEStronglyMeasurable
        (fun x => (inwardDilation n (standardInwardScale k) w x) j)
        volume := by
    have hqm := Measure.quasiMeasurePreserving_smul
      (volume : Measure (GLEuclidean n))
      (inv_ne_zero (standardInwardScale_pos k).ne')
    have hwa : AEStronglyMeasurable
        (inwardDilation n (standardInwardScale k) w) volume :=
      U.zeroTrace.1.comp_quasiMeasurePreserving hqm
    exact (EuclideanSpace.proj j).continuous.aestronglyMeasurable.comp_aemeasurable
      hwa.aemeasurable
  have hfirst (j : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => φ j k x -
        (inwardDilation n (standardInwardScale k) w x) j)
      4 volume) atTop (nhds 0) := by
    refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ζ hζ
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hε ζ hζ] with k hk
    exact (hFour j k).trans hk
  have hsecond (j : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => (inwardDilation n (standardInwardScale k) w x) j - (w x) j)
      4 volume) atTop (nhds 0) := by
    simpa only [w] using U.inward_zeroTrace_component_L4_tendsto base j
  refine ⟨φ, hSmooth, hCompact, hSupport, ?_, ?_⟩
  · intro j
    have hbound (k : ℕ) :
        eLpNorm (fun x => φ j k x - (w x) j) 4 volume ≤
          eLpNorm (fun x => φ j k x -
            (inwardDilation n (standardInwardScale k) w x) j) 4 volume +
          eLpNorm (fun x =>
            (inwardDilation n (standardInwardScale k) w x) j - (w x) j)
            4 volume := by
      have hEq : (fun x => φ j k x - (w x) j) =
          (fun x => φ j k x -
            (inwardDilation n (standardInwardScale k) w x) j) +
          (fun x =>
            (inwardDilation n (standardInwardScale k) w x) j - (w x) j) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rw [hEq]
      exact eLpNorm_add_le
        ((hSmooth j k).continuous.aestronglyMeasurable.sub (hWaCoord j k))
        ((hWaCoord j k).sub (hWcoord j)) (by norm_num)
    have hsum := (hfirst j).add (hsecond j)
    have hlim : Tendsto (fun k => eLpNorm
        (fun x => φ j k x - (w x) j) 4 volume)
        atTop (nhds 0) := by
      refine ENNReal.tendsto_nhds_zero.2 ?_
      intro ζ hζ
      have hsum' : Tendsto (fun k =>
          eLpNorm (fun x => φ j k x -
            (inwardDilation n (standardInwardScale k) w x) j) 4 volume +
          eLpNorm (fun x =>
            (inwardDilation n (standardInwardScale k) w x) j - (w x) j)
            4 volume) atTop (nhds 0) := by
        simpa using hsum
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum' ζ hζ] with k hk
      exact (hbound k).trans hk
    simpa only [w] using hlim
  · intro j i
    let ei : GLEuclidean n := EuclideanSpace.single i (1 : ℝ)
    let G := zeroExtendedGradientDifference n R U.field.grad base.grad
    have hGcoord : AEStronglyMeasurable (fun x => (G x ei) j) volume :=
      (U.zeroTrace.gradient_component_memLp_two j i).aestronglyMeasurable
    have hGaCoord (k : ℕ) : AEStronglyMeasurable
        (fun x => (inwardGradient n (standardInwardScale k) G x ei) j)
        volume := by
      have hqm := Measure.quasiMeasurePreserving_smul
        (volume : Measure (GLEuclidean n))
        (inv_ne_zero (standardInwardScale_pos k).ne')
      have hmeas : AEStronglyMeasurable
          (fun x => (G ((standardInwardScale k)⁻¹ • x) ei) j)
          volume := hGcoord.comp_quasiMeasurePreserving hqm
      simpa only [inwardGradient, ContinuousLinearMap.smul_apply,
        Pi.smul_apply, smul_eq_mul] using
        hmeas.const_mul ((standardInwardScale k)⁻¹)
    have hDeriv (k : ℕ) : Continuous
        (fun x => (fderiv ℝ (φ j k) x) ei) :=
      ((hSmooth j k).continuous_fderiv (by simp)).clm_apply continuous_const
    have hErrMeas (k : ℕ) : AEStronglyMeasurable
        (fun x => (fderiv ℝ (φ j k) x) ei -
          (inwardGradient n (standardInwardScale k) G x ei) j)
        volume := (hDeriv k).aestronglyMeasurable.sub (hGaCoord k)
    have hFirstE : Tendsto (fun k => eLpNorm
        (fun x => (fderiv ℝ (φ j k) x) ei -
          (inwardGradient n (standardInwardScale k) G x ei) j)
        2 volume) atTop (nhds 0) := by
      refine ENNReal.tendsto_nhds_zero.2 ?_
      intro ζ hζ
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hε ζ hζ] with k hk
      exact (hGrad j i k).trans hk
    have hFirst : Tendsto (fun k => lpNorm
        (fun x => (fderiv ℝ (φ j k) x) ei -
          (inwardGradient n (standardInwardScale k) G x ei) j)
        2 volume) atTop (nhds 0) := by
      have ht :=
        (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hFirstE
      have hEq :
          (ENNReal.toReal ∘ fun k => eLpNorm
            (fun x => (fderiv ℝ (φ j k) x) ei -
              (inwardGradient n (standardInwardScale k) G x ei) j)
            2 volume) =
          (fun k => lpNorm
            (fun x => (fderiv ℝ (φ j k) x) ei -
              (inwardGradient n (standardInwardScale k) G x ei) j)
            2 volume) := by
        funext k
        exact toReal_eLpNorm (hErrMeas k)
      rw [hEq] at ht
      simpa using ht
    have hSecond : Tendsto (fun k => lpNorm
        (fun x => (inwardGradient n (standardInwardScale k) G x ei) j -
          (G x ei) j) 2 volume) atTop (nhds 0) := by
      simpa only [G, ei] using
        U.inward_zeroTrace_gradient_component_L2_tendsto base j i
    have hFirstMemLp (k : ℕ) : MemLp
        (fun x => (fderiv ℝ (φ j k) x) ei -
          (inwardGradient n (standardInwardScale k) G x ei) j)
        2 volume := by
      refine ⟨hErrMeas k, ?_⟩
      exact lt_of_le_of_lt (hGrad j i k) (by finiteness)
    have hBound (k : ℕ) : lpNorm
        (fun x => (fderiv ℝ (φ j k) x) ei - (G x ei) j)
        2 volume ≤
      lpNorm (fun x => (fderiv ℝ (φ j k) x) ei -
        (inwardGradient n (standardInwardScale k) G x ei) j) 2 volume +
      lpNorm (fun x => (inwardGradient n (standardInwardScale k) G x ei) j -
        (G x ei) j) 2 volume := by
      have hEq : (fun x => (fderiv ℝ (φ j k) x) ei - (G x ei) j) =
          (fun x => (fderiv ℝ (φ j k) x) ei -
            (inwardGradient n (standardInwardScale k) G x ei) j) +
          (fun x => (inwardGradient n (standardInwardScale k) G x ei) j -
            (G x ei) j) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rw [hEq]
      exact lpNorm_add_le (hFirstMemLp k) (by norm_num)
    have hLim : Tendsto (fun k => lpNorm
        (fun x => (fderiv ℝ (φ j k) x) ei - (G x ei) j)
        2 volume) atTop (nhds 0) := by
      apply squeeze_zero
      · intro k
        exact lpNorm_nonneg
      · exact hBound
      · simpa using hFirst.add hSecond
    simpa only [ei, G] using hLim

end

end BrezisOP6
