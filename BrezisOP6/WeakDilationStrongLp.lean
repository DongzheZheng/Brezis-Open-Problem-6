import BrezisOP6.WeakToDeGiorgi

/-!
# Strong Lebesgue continuity of inward dilations

The first lemma records an exact feature of the Haar Jacobian: an inward
pullback is a contraction on every `Lᵖ` space. The subsequent density
argument will use this uniform bound to pass continuity from compactly
supported smooth maps to arbitrary Lebesgue fields.
-/

namespace BrezisOP6

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

noncomputable section

/-- For `0<a≤1`, precomposition with `x↦a⁻¹x` does not increase the
whole-space `Lᵖ` seminorm. -/
theorem eLpNorm_inwardDilation_le {n : ℕ}
    {F : Type*} [NormedAddCommGroup F]
    (f : GLEuclidean n → F)
    (hf : AEStronglyMeasurable f volume)
    (p : ℝ≥0∞) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    eLpNorm (fun x => f (a⁻¹ • x)) p volume ≤ eLpNorm f p volume := by
  have hpow : a ^ n ≤ 1 := by
    calc
      a ^ n ≤ (1 : ℝ) ^ n := by gcongr
      _ = 1 := one_pow n
  have hc : ENNReal.ofReal (abs ((a⁻¹) ^ n)⁻¹) ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos (inv_pos.mpr ha) n)),
      inv_pow, inv_inv]
    exact (ENNReal.ofReal_le_ofReal hpow).trans (by simp)
  have hmap : Measure.map (fun x : GLEuclidean n => a⁻¹ • x) volume ≤
      volume := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero ha.ne')]
    intro s
    simp only [show Module.finrank ℝ (GLEuclidean n) = n by simp,
      Measure.smul_apply]
    calc
      ENNReal.ofReal (abs ((a⁻¹) ^ n)⁻¹) * volume s ≤
          1 * volume s := by gcongr
      _ = volume s := one_mul _
  have hmapMeas : AEStronglyMeasurable f
      (Measure.map (fun x : GLEuclidean n => a⁻¹ • x) volume) :=
    AEStronglyMeasurable.mono_ac (Measure.absolutelyContinuous_of_le hmap) hf
  calc
    eLpNorm (fun x => f (a⁻¹ • x)) p volume =
        eLpNorm f p (Measure.map (fun x : GLEuclidean n => a⁻¹ • x)
          volume) := by
            symm
            exact eLpNorm_map_measure hmapMeas
              (measurable_const_smul a⁻¹).aemeasurable
    _ ≤ eLpNorm f p volume := eLpNorm_mono_measure f hmap

/-- A compactly supported continuous scalar field is strongly continuous
under inward dilation.  The conclusion is stated in an epsilon--delta
form so it can be combined directly with Sobolev density. -/
theorem exists_delta_eLpNorm_inward_sub_of_continuous_compact
    {n : ℕ} [NeZero n]
    {g : GLEuclidean n → ℝ} (hg : Continuous g)
    (hgCompact : HasCompactSupport g)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃a : ℝ⦄, 1 - δ < a → a < 1 →
        eLpNorm (fun x => g (a⁻¹ • x) - g x) p volume <
          ENNReal.ofReal ε := by
  obtain ⟨r, hr⟩ := hgCompact.isCompact.isBounded.subset_ball
    (0 : GLEuclidean n)
  let M : ℝ := max r 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  let B : Set (GLEuclidean n) := Metric.ball 0 M
  let μB : Measure (GLEuclidean n) := volume.restrict B
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hgSupport : Function.support g ⊆ B := by
    intro x hx
    have hts : x ∈ tsupport g := subset_closure hx
    have hnorm : ‖x‖ < r := by
      simpa [Metric.mem_ball, dist_zero_right] using hr hts
    have : ‖x‖ < M := hnorm.trans_le (le_max_left r 1)
    simpa [B, Metric.mem_ball, dist_zero_right] using this
  have hμBfin : μB Set.univ < ⊤ := by
    simpa [μB, B] using (measure_ball_lt_top : volume B < ⊤)
  have hOneFin : eLpNorm (fun _ : GLEuclidean n => (1 : ℝ)) p μB ≠ ⊤ := by
    exact ((eLpNorm_const_lt_top_iff (μ := μB) (p := p) (c := (1 : ℝ))
      hp0 hpTop).2 (Or.inr hμBfin)).ne
  let K : ℝ := (eLpNorm (fun _ : GLEuclidean n => (1 : ℝ)) p μB).toReal
  have hKnonneg : 0 ≤ K := ENNReal.toReal_nonneg
  let η : ℝ := ε / (2 * (K + 1))
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hOneEq : eLpNorm (fun _ : GLEuclidean n => (1 : ℝ)) p μB =
      ENNReal.ofReal K := by
    exact (ENNReal.ofReal_toReal hOneFin).symm
  have hConstEq : eLpNorm (fun _ : GLEuclidean n => η) p μB =
      ENNReal.ofReal (η * K) := by
    rw [show (fun _ : GLEuclidean n => η) =
      η • (fun _ : GLEuclidean n => (1 : ℝ)) by ext x; simp,
      eLpNorm_const_smul, hOneEq]
    rw [ENNReal.ofReal_mul hηpos.le]
    simp [Real.enorm_eq_ofReal, hηpos.le]
  have hConstLt : eLpNorm (fun _ : GLEuclidean n => η) p μB <
      ENNReal.ofReal ε := by
    rw [hConstEq]
    refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
    have hden : 0 < 2 * (K + 1) := by positivity
    have : K / (2 * (K + 1)) < (1 : ℝ) := by
      apply (div_lt_iff₀ hden).2
      linarith
    calc
      η * K = ε * (K / (2 * (K + 1))) := by
        dsimp [η]; field_simp [hden.ne']
      _ < ε * 1 := by gcongr
      _ = ε := by ring
  have hUC : UniformContinuousOn g (Metric.closedBall 0 (2 * M)) :=
    (isCompact_closedBall (0 : GLEuclidean n) (2 * M)).uniformContinuousOn_of_continuous
      hg.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hUC η hηpos with ⟨ρ, hρpos, hρ⟩
  let δ : ℝ := min (1 / 2) (ρ / (4 * M))
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδpos, ?_⟩
  intro a haNear ha1
  have haHalf : 1 / 2 < a := by
    have hδHalf : δ ≤ 1 / 2 := min_le_left _ _
    linarith
  have ha : 0 < a := by linarith
  have haOne : a ≤ 1 := ha1.le
  have hInvOne : 1 ≤ a⁻¹ := (one_le_inv₀ ha).2 haOne
  have hInvTwo : a⁻¹ < 2 := by
    have hprod : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
    have hInvPos : 0 < a⁻¹ := inv_pos.mpr ha
    nlinarith [mul_pos (by linarith : 0 < 2 * a - 1) hInvPos]
  have hDeltaRho : 2 * (1 - a) * M < ρ := by
    have hδRho : δ ≤ ρ / (4 * M) := min_le_right _ _
    have hsmall : 1 - a < δ := by linarith
    have hfour : 0 < 4 * M := by positivity
    have hbound : 2 * δ * M ≤ ρ / 2 := by
      have hh := (mul_le_mul_of_nonneg_right hδRho (by positivity : 0 ≤ 2 * M))
      have hmul : ρ / (4 * M) * (2 * M) = ρ / 2 := by
        field_simp [hMpos.ne']; ring
      nlinarith
    nlinarith
  have hgDilSupport : Function.support (fun x => g (a⁻¹ • x)) ⊆ B := by
    intro x hx
    by_contra hnot
    have hxNorm : M ≤ ‖x‖ := by
      have hn : ¬ ‖x‖ < M := by
        simpa [B, Metric.mem_ball, dist_zero_right] using hnot
      exact le_of_not_gt hn
    have hscaled : M ≤ ‖a⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      have hh := mul_le_mul_of_nonneg_right hInvOne (norm_nonneg x)
      nlinarith
    have hnotDil : a⁻¹ • x ∉ B := by
      simpa [B, Metric.mem_ball, dist_zero_right] using (not_lt.mpr hscaled)
    exact hnotDil (hgSupport hx)
  have hpoint : ∀ x : GLEuclidean n,
      dist (g (a⁻¹ • x)) (g x) ≤ η := by
    intro x
    by_cases hx : x ∈ B
    · have hxNorm : ‖x‖ < M := by
        simpa [B, Metric.mem_ball, dist_zero_right] using hx
      have hxClosed : x ∈ Metric.closedBall 0 (2 * M) := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        linarith
      have hxDilClosed : a⁻¹ • x ∈ Metric.closedBall 0 (2 * M) := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hInvTwo.le) (norm_nonneg x)]
      have hdist : dist (a⁻¹ • x) x < ρ := by
        rw [dist_eq_norm]
        have hvec : a⁻¹ • x - x = (a⁻¹ - 1) • x := by
          simpa [one_smul] using (sub_smul a⁻¹ (1 : ℝ) x).symm
        rw [hvec, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hInvOne)]
        have hratio : a⁻¹ - 1 ≤ 2 * (1 - a) := by
          have hprod : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
          nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * a - 1)
            (by linarith : 0 ≤ 1 - a)]
        calc
          (a⁻¹ - 1) * ‖x‖ ≤ (a⁻¹ - 1) * M := by
            exact mul_le_mul_of_nonneg_left hxNorm.le
              (sub_nonneg.mpr hInvOne)
          _ ≤ 2 * (1 - a) * M :=
            mul_le_mul_of_nonneg_right hratio hMpos.le
          _ < ρ := hDeltaRho
      exact (hρ _ hxDilClosed _ hxClosed hdist).le
    · have hzero : g x = 0 := by
        by_contra hne
        exact hx (hgSupport hne)
      have hzeroDil : g (a⁻¹ • x) = 0 := by
        by_contra hne
        exact hx (hgDilSupport hne)
      simp [hzero, hzeroDil, hηpos.le]
  have hOnePow : volume B ^ (1 / p.toReal) =
      eLpNorm (fun _ : GLEuclidean n => (1 : ℝ)) p μB := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hBmeas,
      eLpNorm_indicator_const hBmeas hp0 hpTop]
    simp
  have hBound := eLpNorm_sub_le_of_dist_bdd
    (μ := volume) (p := p) hpTop hBmeas hηpos.le hpoint
    hgDilSupport hgSupport
  calc
    eLpNorm (fun x => g (a⁻¹ • x) - g x) p volume ≤
        ENNReal.ofReal η * volume B ^ (1 / p.toReal) := hBound
    _ = eLpNorm (fun _ : GLEuclidean n => η) p μB := by
      rw [hOnePow, hOneEq, hConstEq, ENNReal.ofReal_mul hηpos.le]
    _ < ENNReal.ofReal ε := hConstLt

/-- The inward dilation semigroup is strongly continuous at the identity
on all whole-space scalar `Lᵖ` fields. The proof reduces to a compactly
supported smooth field using the genuine Mathlib `Lᵖ` density theorem,
then uses the contraction above; no pointwise regularity of `f` is assumed. -/
theorem exists_delta_eLpNorm_inward_sub_of_memLp
    {n : ℕ} [NeZero n]
    {f : GLEuclidean n → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp1 : 1 ≤ p) (hpTop : p ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃a : ℝ⦄, 1 - δ < a → a < 1 →
        eLpNorm (fun x => f (a⁻¹ • x) - f x) p volume <
          ENNReal.ofReal ε := by
  let εr : ℝ := ε / 8
  have hεr : 0 < εr := by dsimp [εr]; positivity
  obtain ⟨g, hgCompact, hgSmooth, hfg⟩ :=
    hf.exist_eLpNorm_sub_le hpTop hp1 hεr
  have hg : Continuous g := hgSmooth.continuous
  have hfgMeas : AEStronglyMeasurable (f - g) volume :=
    hf.aestronglyMeasurable.sub hg.aestronglyMeasurable
  obtain ⟨δ₀, hδ₀, hmid⟩ :=
    exists_delta_eLpNorm_inward_sub_of_continuous_compact
      hg hgCompact p (by exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp1))
      hpTop (show 0 < ε / 2 by positivity)
  let δ : ℝ := min δ₀ (1 / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro a haNear ha1
  have ha : 0 < a := by
    have hδHalf : δ ≤ 1 / 2 := min_le_right _ _
    linarith
  have haOne : a ≤ 1 := ha1.le
  have haNear₀ : 1 - δ₀ < a := by
    have hδLe : δ ≤ δ₀ := min_le_left _ _
    linarith
  let A : GLEuclidean n → ℝ := fun x => (f - g) (a⁻¹ • x)
  let B : GLEuclidean n → ℝ := fun x => g (a⁻¹ • x) - g x
  let C : GLEuclidean n → ℝ := fun x => g x - f x
  have hqm := Measure.quasiMeasurePreserving_smul
    (volume : Measure (GLEuclidean n)) (inv_ne_zero ha.ne')
  have hAmeas : AEStronglyMeasurable A volume :=
    hfgMeas.comp_quasiMeasurePreserving hqm
  have hBmeas : AEStronglyMeasurable B volume :=
    ((hg.comp (by fun_prop)).sub hg).aestronglyMeasurable
  have hCmeas : AEStronglyMeasurable C volume :=
    hg.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have hEq : (fun x => f (a⁻¹ • x) - f x) =
      fun x => A x + (B x + C x) := by
    funext x
    dsimp [A, B, C]
    ring
  have hA : eLpNorm A p volume ≤ ENNReal.ofReal εr := by
    exact (eLpNorm_inwardDilation_le (f - g) hfgMeas p a ha haOne).trans hfg
  have hC : eLpNorm C p volume ≤ ENNReal.ofReal εr := by
    have hnorm : ∀ x, ‖C x‖ = ‖(f - g) x‖ := by
      intro x
      simp [C, Pi.sub_apply, norm_sub_rev]
    rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hnorm)]
    exact hfg
  have hB : eLpNorm B p volume < ENNReal.ofReal (ε / 2) :=
    hmid haNear₀ ha1
  have htotal : eLpNorm (fun x => f (a⁻¹ • x) - f x) p volume ≤
      eLpNorm A p volume + (eLpNorm B p volume + eLpNorm C p volume) := by
    rw [hEq]
    calc
      eLpNorm (fun x => A x + (B x + C x)) p volume ≤
          eLpNorm A p volume + eLpNorm (fun x => B x + C x) p volume :=
        eLpNorm_add_le hAmeas (hBmeas.add hCmeas) hp1
      _ ≤ eLpNorm A p volume +
            (eLpNorm B p volume + eLpNorm C p volume) := by
          gcongr
          exact eLpNorm_add_le hBmeas hCmeas hp1
  calc
    eLpNorm (fun x => f (a⁻¹ • x) - f x) p volume ≤
        eLpNorm A p volume +
          (eLpNorm B p volume + eLpNorm C p volume) := htotal
    _ ≤ ENNReal.ofReal εr +
          (eLpNorm B p volume + ENNReal.ofReal εr) := by gcongr
    _ < ENNReal.ofReal εr +
          (ENNReal.ofReal (ε / 2) + ENNReal.ofReal εr) := by
            apply ENNReal.add_lt_add_left ENNReal.ofReal_ne_top
            exact ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hB
    _ < ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_lt_ofReal_iff hε |>.2
      dsimp [εr]
      linarith

/-- Sequential form of strong continuity of inward dilation. -/
theorem eLpNorm_inward_sub_tendsto_of_memLp
    {n : ℕ} [NeZero n]
    {f : GLEuclidean n → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp1 : 1 ≤ p) (hpTop : p ≠ ⊤)
    (a : ℕ → ℝ) (_ha : ∀ k, 0 < a k) (ha1 : ∀ k, a k < 1)
    (hat : Tendsto a atTop (nhds 1)) :
    Tendsto (fun k => eLpNorm
      (fun x => f ((a k)⁻¹ • x) - f x) p volume)
      atTop (nhds 0) := by
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ζ hζ
  obtain ⟨ε, hε, hεζ⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < ζ := by
    by_cases hζTop : ζ = ⊤
    · exact ⟨1, one_pos, hζTop ▸ ENNReal.ofReal_lt_top⟩
    · have hζFin : ζ < ⊤ := lt_top_iff_ne_top.mpr hζTop
      refine ⟨(ζ / 2).toReal,
        ENNReal.toReal_pos
          (ENNReal.div_pos hζ.ne' (by norm_num)).ne'
          (ENNReal.div_lt_top hζFin.ne (by norm_num)).ne,
        ?_⟩
      calc
        ENNReal.ofReal (ζ / 2).toReal = ζ / 2 :=
          ENNReal.ofReal_toReal
            (ENNReal.div_lt_top hζFin.ne (by norm_num)).ne
        _ < ζ := ENNReal.half_lt_self hζ.ne' hζTop
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_delta_eLpNorm_inward_sub_of_memLp hf hp1 hpTop hε
  have hev : ∀ᶠ k in atTop, 1 - δ < a k :=
    hat.eventually (Ioi_mem_nhds (by linarith : 1 - δ < (1 : ℝ)))
  filter_upwards [hev] with k hk
  exact (hsmall hk (ha1 k)).le.trans hεζ.le

/-- A concrete sequence of inward factors approaching the identity. -/
def standardInwardScale (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) / ((k : ℝ) + 2)

theorem standardInwardScale_pos (k : ℕ) : 0 < standardInwardScale k := by
  unfold standardInwardScale
  positivity

theorem standardInwardScale_lt_one (k : ℕ) : standardInwardScale k < 1 := by
  unfold standardInwardScale
  apply (div_lt_iff₀ (by positivity : 0 < (k : ℝ) + 2)).2
  linarith

theorem standardInwardScale_tendsto_one :
    Tendsto standardInwardScale atTop (nhds 1) := by
  have hdiv : Tendsto
      (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hshift : Tendsto
      (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (nhds 0) := by
    have hfun :
        ((fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) ∘
          (fun k : ℕ => k + 1)) =
        (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) := by
      funext k
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    simpa only [hfun] using hdiv.comp (tendsto_add_atTop_nat 1)
  have hsub : Tendsto
      (fun k : ℕ => (1 : ℝ) - (1 : ℝ) / ((k : ℝ) + 2))
      atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hshift
  have hEq (k : ℕ) :
      standardInwardScale k = 1 - (1 : ℝ) / ((k : ℝ) + 2) := by
    unfold standardInwardScale
    have hden : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hden]
    ring
  simpa only [sub_zero, ← hEq] using hsub

/-- The actual weak derivative of an inward dilation includes the factor
`a⁻¹`. Strong `Lᵖ` continuity survives this factor. -/
theorem lpNorm_inwardGradient_sub_tendsto_of_memLp
    {n : ℕ} [NeZero n]
    {f : GLEuclidean n → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hp1 : 1 ≤ p) (hpTop : p ≠ ⊤)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (ha1 : ∀ k, a k < 1)
    (hat : Tendsto a atTop (nhds 1)) :
    Tendsto (fun k => lpNorm
      (fun x => (a k)⁻¹ * f ((a k)⁻¹ • x) - f x) p volume)
      atTop (nhds 0) := by
  let D : ℕ → GLEuclidean n → ℝ :=
    fun k x => f ((a k)⁻¹ • x)
  have hD (k : ℕ) : MemLp (D k) p volume := by
    have hqm := Measure.quasiMeasurePreserving_smul
      (volume : Measure (GLEuclidean n)) (inv_ne_zero (ha k).ne')
    have hmeas : AEStronglyMeasurable (D k) volume :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqm
    refine ⟨hmeas, ?_⟩
    exact (eLpNorm_inwardDilation_le f hf.aestronglyMeasurable p
      (a k) (ha k) (ha1 k).le).trans_lt hf.eLpNorm_lt_top
  have hDsub (k : ℕ) : MemLp (fun x => D k x - f x) p volume :=
    (hD k).sub hf
  have hDnorm (k : ℕ) : lpNorm (D k) p volume ≤ lpNorm f p volume := by
    have hbound := eLpNorm_inwardDilation_le f hf.aestronglyMeasurable p
      (a k) (ha k) (ha1 k).le
    have hre := ENNReal.toReal_mono hf.eLpNorm_ne_top hbound
    simpa [D, toReal_eLpNorm (hD k).aestronglyMeasurable,
      toReal_eLpNorm hf.aestronglyMeasurable] using hre
  have hDsubE :=
    eLpNorm_inward_sub_tendsto_of_memLp hf hp1 hpTop a ha ha1 hat
  have hDsubReal : Tendsto
      (fun k => lpNorm (fun x => D k x - f x) p volume)
      atTop (nhds 0) := by
    have h := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hDsubE
    have hfun :
        (ENNReal.toReal ∘
          fun k => eLpNorm
            (fun x => f ((a k)⁻¹ • x) - f x) p volume) =
          (fun k => lpNorm (fun x => D k x - f x) p volume) := by
      funext k
      exact toReal_eLpNorm (hDsub k).aestronglyMeasurable
    rw [hfun] at h
    simpa using h
  have hInv : Tendsto (fun k => (a k)⁻¹) atTop (nhds (1 : ℝ)) := by
    simpa using ((continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hat)
  have hCoef : Tendsto (fun k => |(a k)⁻¹ - 1|) atTop (nhds 0) := by
    have hh : Tendsto (fun k => (a k)⁻¹ - 1) atTop (nhds (0 : ℝ)) := by
      simpa using hInv.sub_const 1
    simpa using hh.abs
  have hCoefNorm : Tendsto
      (fun k => |(a k)⁻¹ - 1| * lpNorm f p volume)
      atTop (nhds 0) := by
    simpa using hCoef.mul_const (lpNorm f p volume)
  have hbound (k : ℕ) :
      lpNorm (fun x => (a k)⁻¹ * D k x - f x) p volume ≤
        |(a k)⁻¹ - 1| * lpNorm f p volume +
          lpNorm (fun x => D k x - f x) p volume := by
    have hfirst : MemLp
        (fun x => ((a k)⁻¹ - 1) * D k x) p volume := by
      simpa [smul_eq_mul, Pi.smul_apply] using
        (hD k).const_smul ((a k)⁻¹ - 1)
    have hident :
        (fun x => (a k)⁻¹ * D k x - f x) =
          (fun x => ((a k)⁻¹ - 1) * D k x) +
            (fun x => D k x - f x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [hident]
    calc
      lpNorm
          ((fun x => ((a k)⁻¹ - 1) * D k x) +
            (fun x => D k x - f x)) p volume ≤
          lpNorm (fun x => ((a k)⁻¹ - 1) * D k x) p volume +
            lpNorm (fun x => D k x - f x) p volume :=
        lpNorm_add_le hfirst hp1
      _ = |(a k)⁻¹ - 1| * lpNorm (D k) p volume +
            lpNorm (fun x => D k x - f x) p volume := by
          rw [show (fun x => ((a k)⁻¹ - 1) * D k x) =
            ((a k)⁻¹ - 1) • D k by funext x; simp [Pi.smul_apply, smul_eq_mul],
            lpNorm_const_smul]
          simp [Real.norm_eq_abs]
      _ ≤ |(a k)⁻¹ - 1| * lpNorm f p volume +
            lpNorm (fun x => D k x - f x) p volume := by
          gcongr
          exact hDnorm k
  have hsum : Tendsto
      (fun k => |(a k)⁻¹ - 1| * lpNorm f p volume +
        lpNorm (fun x => D k x - f x) p volume)
      atTop (nhds 0) := by
    simpa using hCoefNorm.add hDsubReal
  apply squeeze_zero
  · intro k
    exact lpNorm_nonneg
  · exact hbound
  · exact hsum

end

end BrezisOP6
