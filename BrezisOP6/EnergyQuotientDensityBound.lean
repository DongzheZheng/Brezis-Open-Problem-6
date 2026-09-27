import BrezisOP6.EnergyQuotientGradientBound
import BrezisOP6.EnergyCriticalKernel

/-!
# Algebra of the quotient-energy singularity

The single-profile energy density can be expressed with three nonnegative
quantities: `W=p²|∇z|²`, `Z=|w|²=p²|z|²`, and `P=p²`.  This removes the
apparent fourth-order quotient pole from the potential term.  The lemma
below isolates the precise inverse-square majorant before it is connected
to smooth numerator and profile bounds.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- Squared norm of the Fréchet derivative is measurable for every field,
since mathlib's `fderiv` uses the zero value at nondifferentiability points. -/
theorem measurable_euclideanGradientSq (n : ℕ)
    (u : GLEuclidean n → GLEuclidean n) :
    Measurable (euclideanGradientSq n u) := by
  unfold euclideanGradientSq
  fun_prop

/-- A measurable profile and numerator give a measurable reduced density,
including at points where the quotient is not differentiable. -/
theorem measurable_singleProfileDensity_quotient (m : ℕ)
    (p : ℝ → ℝ) (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hp : Measurable p) (hw : Measurable w) :
    Measurable
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • w y))
        (fun y => ‖(p ‖y‖)⁻¹ • w y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2)) := by
  have hz : Measurable
      (fun y : GLEuclidean (m + 3) => (p ‖y‖)⁻¹ • w y) := by
    fun_prop
  have hgrad := measurable_euclideanGradientSq (m + 3)
    (fun y : GLEuclidean (m + 3) => (p ‖y‖)⁻¹ • w y)
  unfold singleProfileDensity
  fun_prop

/-- Away from the origin, continuity of the quotient and its actual
Fréchet derivative makes the reduced density continuous. -/
theorem singleProfileDensity_continuousOn (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (s : Set (GLEuclidean (m + 3)))
    (hs0 : ∀ x ∈ s, x ≠ 0)
    (hp : ContinuousOn (fun x : GLEuclidean (m + 3) => p ‖x‖) s)
    (hz : ContinuousOn z s)
    (hdz : ContinuousOn (fderiv ℝ z) s) :
    ContinuousOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2)) s := by
  have hgrad := euclideanGradientSq_continuousOn_of_fderiv
    (m + 3) z s hdz
  have hnorm : ContinuousOn
      (fun y : GLEuclidean (m + 3) => ‖y‖) s :=
    continuousOn_id.norm
  have hq : ContinuousOn
      (fun y : GLEuclidean (m + 3) => ‖y‖⁻¹ ^ 2) s := by
    exact (hnorm.inv₀ (fun x hx =>
      norm_ne_zero_iff.mpr (hs0 x hx))).pow 2
  have hzsq : ContinuousOn (fun y => ‖z y‖ ^ 2) s := hz.norm.pow 2
  have hlinear : ContinuousOn
      (fun y => euclideanGradientSq (m + 3) z y -
        (((m + 3 : ℕ) : ℝ) - 1) * ‖y‖⁻¹ ^ 2 * ‖z y‖ ^ 2) s :=
    hgrad.sub ((continuousOn_const.mul hq).mul hzsq)
  have hpotential : ContinuousOn
      (fun y => (‖z y‖ ^ 2 - 1) ^ 2) s :=
    (hzsq.sub continuousOn_const).pow 2
  simpa only [singleProfileDensity] using
    (((hp.pow 2).mul hlinear).div_const 2).add
      (((hp.pow 4).mul hpotential).div_const 4)

/-- A scalar bound for the reduced Ginzburg--Landau density.  If the
weighted quotient gradient has an inverse-square bound, so does the full
density; the potential term stays uniformly bounded. -/
theorem quotient_density_algebra_bound
    (a W Z P q K0 K2 Zmax Pmax : ℝ)
    (ha : 0 ≤ a) (hW0 : 0 ≤ W) (hZ0 : 0 ≤ Z)
    (hP0 : 0 ≤ P) (hq : 0 ≤ q)
    (hZmax : 0 ≤ Zmax) (hPmax : 0 ≤ Pmax)
    (hW : W ≤ K0 + K2 * q)
    (hZ : Z ≤ Zmax) (hP : P ≤ Pmax) :
    |(W - a * q * Z) / 2 + (Z - P) ^ 2 / 4| ≤
      (K0 + (K2 + a * Zmax) * q) / 2 +
        (Zmax + Pmax) ^ 2 / 4 := by
  have haqZ : 0 ≤ a * q * Z :=
    mul_nonneg (mul_nonneg ha hq) hZ0
  have hlinear : |W - a * q * Z| ≤ W + a * q * Z := by
    calc
      _ = |W + -(a * q * Z)| := by ring
      _ ≤ |W| + |-(a * q * Z)| := abs_add_le _ _
      _ = |W| + |a * q * Z| := by rw [abs_neg]
      _ = _ := by rw [abs_of_nonneg hW0, abs_of_nonneg haqZ]
  have hZP : |Z - P| ≤ Zmax + Pmax := by
    calc
      _ = |Z + -P| := by ring
      _ ≤ |Z| + |-P| := abs_add_le _ _
      _ = |Z| + |P| := by rw [abs_neg]
      _ = Z + P := by rw [abs_of_nonneg hZ0, abs_of_nonneg hP0]
      _ ≤ Zmax + Pmax := add_le_add hZ hP
  have hquartic : (Z - P) ^ 2 ≤ (Zmax + Pmax) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (Z - P))
      (add_nonneg hZmax hPmax)).2 hZP
    simpa only [sq_abs] using h
  have hcoeff : a * q * Z ≤ a * q * Zmax :=
    mul_le_mul_of_nonneg_left hZ (mul_nonneg ha hq)
  have hlinearBound : W + a * q * Z ≤
      K0 + (K2 + a * Zmax) * q := by
    nlinarith [hW, hcoeff]
  have hfirst : |(W - a * q * Z) / 2| ≤
      (K0 + (K2 + a * Zmax) * q) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (hlinear.trans hlinearBound) (by norm_num)
  have hsecond : |(Z - P) ^ 2 / 4| ≤
      (Zmax + Pmax) ^ 2 / 4 := by
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
    exact div_le_div_of_nonneg_right hquartic (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- The generic inverse-square estimate instantiated on the actual quotient
`z=w/p`.  The apparent fourth-order pole in the potential disappears
because `p²|z|²=|w|²` pointwise.  Thus only an `r⁻²` pole remains in the
reduced density, independently of the behavior of `z` at the origin. -/
theorem singleProfileDensity_quotient_abs_le_inverse_square (m : ℕ)
    (p : ℝ → ℝ) (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3))
    (dp Cdp Cratio Cw Cg Cp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖)
    (hpx : p ‖x‖ ≠ 0) (hwDiff : DifferentiableAt ℝ w x)
    (hCdp : 0 ≤ Cdp) (hCratio : 0 ≤ Cratio)
    (hCw : 0 ≤ Cw) (hCp : 0 ≤ Cp)
    (hdp : |dp| ≤ Cdp)
    (hratio : |‖x‖ / p ‖x‖| ≤ Cratio)
    (hw : ‖w x‖ ≤ Cw) (hgrad : euclideanGradientSq (m + 3) w x ≤ Cg)
    (hpBound : |p ‖x‖| ≤ Cp) :
    |singleProfileDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => p ‖y‖)
      (euclideanGradientSq (m + 3)
        (fun y => (p ‖y‖)⁻¹ • w y))
      (fun y => ‖(p ‖y‖)⁻¹ • w y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x| ≤
      (2 * Cg +
        (2 * Cdp ^ 2 * Cratio ^ 2 * Cw ^ 2 +
          ((m : ℝ) + 2) * Cw ^ 2) * ‖x‖⁻¹ ^ 2) / 2 +
        (Cw ^ 2 + Cp ^ 2) ^ 2 / 4 := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun y => (p ‖y‖)⁻¹ • w y
  let W : ℝ := p ‖x‖ ^ 2 * euclideanGradientSq (m + 3) z x
  let Z : ℝ := p ‖x‖ ^ 2 * ‖z x‖ ^ 2
  let P : ℝ := p ‖x‖ ^ 2
  let q : ℝ := ‖x‖⁻¹ ^ 2
  have hgradNonneg : 0 ≤ euclideanGradientSq (m + 3) z x := by
    unfold euclideanGradientSq
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hW0 : 0 ≤ W := mul_nonneg (sq_nonneg _) hgradNonneg
  have hZ0 : 0 ≤ Z := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hP0 : 0 ≤ P := sq_nonneg _
  have hq : 0 ≤ q := sq_nonneg _
  have hZeq : Z = ‖w x‖ ^ 2 := by
    simp only [Z, z, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hpx]
  have hZ : Z ≤ Cw ^ 2 := by
    rw [hZeq]
    exact (sq_le_sq₀ (norm_nonneg _) hCw).2 hw
  have hP : P ≤ Cp ^ 2 := by
    exact (sq_le_sq).2 (by simpa only [abs_of_nonneg hCp] using hpBound)
  have hW : W ≤ 2 * Cg +
      (2 * Cdp ^ 2 * Cratio ^ 2 * Cw ^ 2) * q := by
    simpa only [W, q, z] using
      energyQuotient_weighted_gradient_le_inverse_square (m + 3)
        p w x dp Cdp Cratio Cw Cg hx hp hpx hwDiff
        hCdp hCratio hCw hdp hratio hw hgrad
  have hAlgebra := quotient_density_algebra_bound
    ((m : ℝ) + 2) W Z P q
    (2 * Cg) (2 * Cdp ^ 2 * Cratio ^ 2 * Cw ^ 2)
    (Cw ^ 2) (Cp ^ 2)
    (by positivity) hW0 hZ0 hP0 hq
    (sq_nonneg _) (sq_nonneg _) hW hZ hP
  have hDensity : singleProfileDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => p ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x =
      (W - ((m : ℝ) + 2) * q * Z) / 2 + (Z - P) ^ 2 / 4 := by
    unfold singleProfileDensity W Z P q
    have hn : (((m + 3 : ℕ) : ℝ) - 1) = (m : ℝ) + 2 := by
      push_cast
      ring
    rw [hn]
    ring
  rw [hDensity]
  simpa only [z, W, Z, P, q] using hAlgebra

/-- On a small ball, regular-origin profile bounds and `C¹` bounds on the
smooth numerator imply integrability of the *actual* single-profile
density.  The only separately supplied analytic input is local
measurability; the magnitude bound is derived here. -/
theorem singleProfileDensity_quotient_integrableOn_ball (m : ℕ)
    (δ : ℝ) (p : ℝ → ℝ)
    (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (Cdp Cratio Cw Cg Cp : ℝ)
    (hp0 : p 0 = 0)
    (hCdp : 0 ≤ Cdp) (hCratio : 0 ≤ Cratio)
    (hCw : 0 ≤ Cw) (hCg : 0 ≤ Cg) (hCp : 0 ≤ Cp)
    (hp : ∀ r : ℝ, 0 < r → r < δ →
      HasDerivAt p (deriv p r) r ∧ p r ≠ 0 ∧
        |deriv p r| ≤ Cdp ∧ |r / p r| ≤ Cratio ∧ |p r| ≤ Cp)
    (hw : ∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) δ,
      DifferentiableAt ℝ w x ∧ ‖w x‖ ≤ Cw ∧
        euclideanGradientSq (m + 3) w x ≤ Cg)
    (hpMeas : Measurable p) (hwMeas : Measurable w) :
    IntegrableOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • w y))
        (fun y => ‖(p ‖y‖)⁻¹ • w y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.ball (0 : GLEuclidean (m + 3)) δ) volume := by
  let D : GLEuclidean (m + 3) → ℝ :=
    singleProfileDensity (m + 3)
      (fun y => p ‖y‖)
      (euclideanGradientSq (m + 3)
        (fun y => (p ‖y‖)⁻¹ • w y))
      (fun y => ‖(p ‖y‖)⁻¹ • w y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2)
  let A : ℝ := Cg + (Cw ^ 2 + Cp ^ 2) ^ 2 / 4
  let B : ℝ :=
    (2 * Cdp ^ 2 * Cratio ^ 2 * Cw ^ 2 +
      ((m : ℝ) + 2) * Cw ^ 2) / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) δ,
      ‖D x‖ ≤ (A + B) * (1 + ‖x‖⁻¹ ^ 2) := by
    intro x hxBall
    by_cases hx0 : x = 0
    · subst x
      have hD : D 0 = 0 := by
        simp [D, singleProfileDensity, hp0]
      simp only [hD, norm_zero, norm_zero, inv_zero, zero_pow (by norm_num : 2 ≠ 0)]
      nlinarith
    have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrδ : ‖x‖ < δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxBall
    obtain ⟨hpderiv, hpne, hdp, hratio, hpb⟩ := hp ‖x‖ hrpos hrδ
    obtain ⟨hwDiff, hwBound, hgrad⟩ := hw x hxBall
    have hDensity := singleProfileDensity_quotient_abs_le_inverse_square
      m p w x (deriv p ‖x‖) Cdp Cratio Cw Cg Cp
      hx0 hpderiv hpne hwDiff hCdp hCratio hCw hCp
      hdp hratio hwBound hgrad hpb
    have hq : 0 ≤ ‖x‖⁻¹ ^ 2 := sq_nonneg _
    have hlinear : ‖D x‖ ≤ A + B * ‖x‖⁻¹ ^ 2 := by
      convert hDensity using 1 <;> dsimp [D, A, B] <;> ring
    have hmajor : A + B * ‖x‖⁻¹ ^ 2 ≤
        (A + B) * (1 + ‖x‖⁻¹ ^ 2) := by
      nlinarith [mul_nonneg hA hq]
    exact hlinear.trans hmajor
  exact integrableOn_ball_of_inverse_square_bound m δ (A + B) D
    (by simpa only [D] using
      (measurable_singleProfileDensity_quotient m p w
        hpMeas hwMeas).aestronglyMeasurable.restrict)
    ((ae_restrict_iff' measurableSet_ball).2
      (Filter.Eventually.of_forall (fun x hx => hpoint x hx)))

/-- The local inverse-square theorem and ordinary continuity on the
remaining annulus discharge the reduced-density field in the
single-profile identity. -/
theorem energyReducedSpatialDensity_quotient_integrableOn_of_inner_outer
    (m : ℕ) (R δ : ℝ) (p : ℝ → ℝ)
    (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hinner : IntegrableOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • w y))
        (fun y => ‖(p ‖y‖)⁻¹ • w y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.ball (0 : GLEuclidean (m + 3)) δ) volume)
    (houter : ContinuousOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • w y))
        (fun y => ‖(p ‖y‖)⁻¹ • w y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R \
        Metric.ball (0 : GLEuclidean (m + 3)) δ)) :
    IntegrableOn
      (energyReducedSpatialDensity m p
        (fun y : GLEuclidean (m + 3) => (p ‖y‖)⁻¹ • w y))
      (energyPositiveClosedBall (m + 3) R) volume := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun y => (p ‖y‖)⁻¹ • w y
  let D : GLEuclidean (m + 3) → ℝ :=
    singleProfileDensity (m + 3)
      (fun y => p ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2)
  have hD : IntegrableOn D
      (energyPositiveClosedBall (m + 3) R) volume :=
    integrableOn_positiveBall_of_inner_continuous_outer m R δ D
      (by simpa only [D, z] using hinner)
      (by simpa only [D, z] using houter)
  apply hD.congr_fun
  · intro x hx
    have hx0 : x ≠ 0 := by
      intro hzero
      subst x
      simp [energyPositiveClosedBall] at hx
    exact (energyReducedSpatialDensity_eq_singleProfileDensity
      m p z x hx0).symm
  · exact measurableSet_energyPositiveClosedBall (m + 3) R

end

end BrezisOP6
