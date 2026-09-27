import BrezisOP6.EnergyConcreteReducedDensity

/-!
# The second profile acting on the shared quotient

For the bridge the quotient is always `z=u/f`.  The second single-profile
identity weights that same field by `F²`.  Under `0≤F≤f`, its weighted
gradient and norm are dominated by the already controlled `f`-weighted
quantities.  Thus the second density has the same inverse-square
majorant without introducing a new transformed numerator.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- Dominance of the profile weight transfers an inverse-square estimate
to the second reduced density.  The only singular term is `q=r⁻²`. -/
theorem shared_quotient_density_algebra_bound
    (m : ℕ) (f F G Z q K0 K2 Zmax Pmax : ℝ)
    (hF2 : 0 ≤ F ^ 2) (hFle : F ^ 2 ≤ f ^ 2)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hq : 0 ≤ q)
    (hZmax : 0 ≤ Zmax) (hPmax : 0 ≤ Pmax)
    (hWG : f ^ 2 * G ≤ K0 + K2 * q)
    (hWZ : f ^ 2 * Z ≤ Zmax)
    (hWP : F ^ 2 ≤ Pmax) :
    |(F ^ 2 * G - ((m : ℝ) + 2) * q * (F ^ 2 * Z)) / 2 +
        (F ^ 2 * Z - F ^ 2) ^ 2 / 4| ≤
      (K0 + (K2 + ((m : ℝ) + 2) * Zmax) * q) / 2 +
        (Zmax + Pmax) ^ 2 / 4 := by
  have hgrad : F ^ 2 * G ≤ K0 + K2 * q :=
    (mul_le_mul_of_nonneg_right hFle hG).trans hWG
  have hnorm : F ^ 2 * Z ≤ Zmax :=
    (mul_le_mul_of_nonneg_right hFle hZ).trans hWZ
  exact quotient_density_algebra_bound
    ((m : ℝ) + 2) (F ^ 2 * G) (F ^ 2 * Z) (F ^ 2) q
    K0 K2 Zmax Pmax
    (by positivity) (mul_nonneg hF2 hG)
    (mul_nonneg hF2 hZ) hF2 hq hZmax hPmax
    hgrad hnorm hWP

/-- Pointwise inverse-square majorant for the *second* profile applied to
the shared quotient `z=u/f`.  No smoothness of a transformed numerator is
needed. -/
theorem shared_quotient_second_density_abs_le_inverse_square
    (m : ℕ) (f F : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3))
    (df Cdf Cratio Cu Cg Cp : ℝ)
    (hx : x ≠ 0) (hfDeriv : HasDerivAt f df ‖x‖)
    (hfx : f ‖x‖ ≠ 0)
    (huDiff : DifferentiableAt ℝ u x)
    (hCdf : 0 ≤ Cdf) (hCratio : 0 ≤ Cratio)
    (hCu : 0 ≤ Cu) (hCp : 0 ≤ Cp)
    (hdf : |df| ≤ Cdf)
    (hratio : |‖x‖ / f ‖x‖| ≤ Cratio)
    (hu : ‖u x‖ ≤ Cu)
    (hgrad : euclideanGradientSq (m + 3) u x ≤ Cg)
    (hfBound : |f ‖x‖| ≤ Cp)
    (hF0 : 0 ≤ F ‖x‖) (hFle : F ‖x‖ ≤ f ‖x‖) :
    |singleProfileDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3)
        (fun y => (f ‖y‖)⁻¹ • u y))
      (fun y => ‖(f ‖y‖)⁻¹ • u y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x| ≤
      (2 * Cg +
        (2 * Cdf ^ 2 * Cratio ^ 2 * Cu ^ 2 +
          ((m : ℝ) + 2) * Cu ^ 2) * ‖x‖⁻¹ ^ 2) / 2 +
        (Cu ^ 2 + Cp ^ 2) ^ 2 / 4 := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun y => (f ‖y‖)⁻¹ • u y
  let G := euclideanGradientSq (m + 3) z x
  let Z := ‖z x‖ ^ 2
  let q := ‖x‖⁻¹ ^ 2
  have hG0 : 0 ≤ G := by
    unfold G euclideanGradientSq
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hZ0 : 0 ≤ Z := sq_nonneg _
  have hq : 0 ≤ q := sq_nonneg _
  have hf0 : 0 ≤ f ‖x‖ := hF0.trans hFle
  have hF2le : F ‖x‖ ^ 2 ≤ f ‖x‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hFle)
      (add_nonneg hf0 hF0)]
  have hF2 : 0 ≤ F ‖x‖ ^ 2 := sq_nonneg _
  have hWG : f ‖x‖ ^ 2 * G ≤
      2 * Cg +
        (2 * Cdf ^ 2 * Cratio ^ 2 * Cu ^ 2) * q := by
    simpa only [G, q, z] using
      energyQuotient_weighted_gradient_le_inverse_square
        (m + 3) f u x df Cdf Cratio Cu Cg
        hx hfDeriv hfx huDiff hCdf hCratio hCu
        hdf hratio hu hgrad
  have hZidentity : f ‖x‖ ^ 2 * Z = ‖u x‖ ^ 2 := by
    simp only [Z, z, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hfx]
  have hWZ : f ‖x‖ ^ 2 * Z ≤ Cu ^ 2 := by
    rw [hZidentity]
    exact (sq_le_sq₀ (norm_nonneg _) hCu).2 hu
  have hWP : F ‖x‖ ^ 2 ≤ Cp ^ 2 := by
    have hfCp : f ‖x‖ ≤ Cp := by
      simpa only [abs_of_nonneg hf0] using hfBound
    have hFCp : F ‖x‖ ≤ Cp := hFle.trans hfCp
    exact (sq_le_sq₀ hF0 hCp).2 hFCp
  have h := shared_quotient_density_algebra_bound m
    (f ‖x‖) (F ‖x‖) G Z q
    (2 * Cg) (2 * Cdf ^ 2 * Cratio ^ 2 * Cu ^ 2)
    (Cu ^ 2) (Cp ^ 2) hF2 hF2le hG0 hZ0 hq
    (sq_nonneg _) (sq_nonneg _) hWG hWZ hWP
  have hD : singleProfileDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x =
      (F ‖x‖ ^ 2 * G - ((m : ℝ) + 2) * q *
        (F ‖x‖ ^ 2 * Z)) / 2 +
        (F ‖x‖ ^ 2 * Z - F ‖x‖ ^ 2) ^ 2 / 4 := by
    unfold singleProfileDensity G Z q
    have hn : (((m + 3 : ℕ) : ℝ) - 1) = (m : ℝ) + 2 := by
      push_cast
      ring
    rw [hn]
    ring
  rw [hD]
  simpa only [z, G, Z, q] using h

/-- The second reduced density has the same critical inverse-square
integrability on a small ball, although its quotient is formed using the
first profile. -/
theorem shared_quotient_second_density_integrableOn_ball
    (m : ℕ) (δ : ℝ) (f F : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (Cdf Cratio Cu Cg Cp : ℝ)
    (hF0 : F 0 = 0)
    (hCdf : 0 ≤ Cdf) (hCratio : 0 ≤ Cratio)
    (hCu : 0 ≤ Cu) (hCg : 0 ≤ Cg) (hCp : 0 ≤ Cp)
    (hf : ∀ r : ℝ, 0 < r → r < δ →
      HasDerivAt f (deriv f r) r ∧ f r ≠ 0 ∧
        |deriv f r| ≤ Cdf ∧ |r / f r| ≤ Cratio ∧ |f r| ≤ Cp)
    (hFle : ∀ r : ℝ, 0 < r → r < δ →
      0 ≤ F r ∧ F r ≤ f r)
    (hu : ∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) δ,
      DifferentiableAt ℝ u x ∧ ‖u x‖ ≤ Cu ∧
        euclideanGradientSq (m + 3) u x ≤ Cg)
    (hfMeas : Measurable f) (hFMeas : Measurable F)
    (huMeas : Measurable u) :
    IntegrableOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (f ‖y‖)⁻¹ • u y))
        (fun y => ‖(f ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.ball (0 : GLEuclidean (m + 3)) δ) volume := by
  let D : GLEuclidean (m + 3) → ℝ :=
    singleProfileDensity (m + 3)
      (fun y => F ‖y‖)
      (euclideanGradientSq (m + 3)
        (fun y => (f ‖y‖)⁻¹ • u y))
      (fun y => ‖(f ‖y‖)⁻¹ • u y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2)
  let A : ℝ := Cg + (Cu ^ 2 + Cp ^ 2) ^ 2 / 4
  let B : ℝ :=
    (2 * Cdf ^ 2 * Cratio ^ 2 * Cu ^ 2 +
      ((m : ℝ) + 2) * Cu ^ 2) / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) δ,
      ‖D x‖ ≤ (A + B) * (1 + ‖x‖⁻¹ ^ 2) := by
    intro x hxBall
    by_cases hx0 : x = 0
    · subst x
      have hD : D 0 = 0 := by
        simp [D, singleProfileDensity, hF0]
      simp only [hD, norm_zero, inv_zero,
        zero_pow (by norm_num : 2 ≠ 0)]
      nlinarith
    have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrδ : ‖x‖ < δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxBall
    obtain ⟨hfderiv, hfne, hdf, hratio, hfb⟩ :=
      hf ‖x‖ hrpos hrδ
    obtain ⟨hFnonneg, hFbound⟩ := hFle ‖x‖ hrpos hrδ
    obtain ⟨huDiff, huBound, hgrad⟩ := hu x hxBall
    have hDensity := shared_quotient_second_density_abs_le_inverse_square
      m f F u x (deriv f ‖x‖) Cdf Cratio Cu Cg Cp
      hx0 hfderiv hfne huDiff hCdf hCratio hCu hCp
      hdf hratio huBound hgrad hfb hFnonneg hFbound
    have hq : 0 ≤ ‖x‖⁻¹ ^ 2 := sq_nonneg _
    have hlinear : ‖D x‖ ≤ A + B * ‖x‖⁻¹ ^ 2 := by
      convert hDensity using 1 <;> dsimp [D, A, B] <;> ring
    have hmajor : A + B * ‖x‖⁻¹ ^ 2 ≤
        (A + B) * (1 + ‖x‖⁻¹ ^ 2) := by
      nlinarith [mul_nonneg hA hq]
    exact hlinear.trans hmajor
  have hzMeas : Measurable
      (fun y : GLEuclidean (m + 3) => (f ‖y‖)⁻¹ • u y) := by
    fun_prop
  have hDMeas : Measurable D := by
    have hgradMeas := measurable_euclideanGradientSq (m + 3)
      (fun y : GLEuclidean (m + 3) => (f ‖y‖)⁻¹ • u y)
    unfold D singleProfileDensity
    fun_prop
  exact integrableOn_ball_of_inverse_square_bound m δ (A + B) D
    hDMeas.aestronglyMeasurable.restrict
    ((ae_restrict_iff' measurableSet_ball).2
      (Filter.Eventually.of_forall (fun x hx => hpoint x hx)))

/-- Ordinary positive-radius continuity for the second profile acting on
the quotient formed by the first. -/
theorem shared_quotient_second_density_continuousOn_positiveBall
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (huC1 : ContDiff ℝ 1 u)
    (hfPos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r) :
    ContinuousOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (f ‖y‖)⁻¹ • u y))
        (fun y => ‖(f ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (energyPositiveClosedBall (m + 3) R) := by
  let E := GLEuclidean (m + 3)
  let s : Set E := {x | 0 < ‖x‖ ∧ f ‖x‖ ≠ 0}
  have hsOpen : IsOpen s := by
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_ne_fun (hfC1.continuous.comp continuous_norm) continuous_const)
  have hn : ContDiffOn ℝ 1 (fun x : E => ‖x‖) s := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hx.1
    exact (contDiffAt_norm ℝ hx0).contDiffWithinAt
  have hfOn : ContDiffOn ℝ 1 (fun x : E => f ‖x‖) s :=
    hfC1.comp_contDiffOn hn
  have hFOn : ContDiffOn ℝ 1 (fun x : E => F ‖x‖) s :=
    hFC1.comp_contDiffOn hn
  have hz : ContDiffOn ℝ 1
      (fun x : E => (f ‖x‖)⁻¹ • u x) s :=
    (hfOn.inv (fun x hx => hx.2)).smul huC1.contDiffOn
  have hsub : energyPositiveClosedBall (m + 3) R ⊆ s := by
    intro x hx
    exact ⟨hx.1, ne_of_gt (hfPos ‖x‖ hx.1 hx.2)⟩
  have hD := singleProfileDensity_continuousOn m F
    (fun x : E => (f ‖x‖)⁻¹ • u x) s
    (fun x hx => norm_pos_iff.mp hx.1)
    hFOn.continuousOn hz.continuousOn
    (hz.continuousOn_fderiv_of_isOpen hsOpen (by norm_num))
  exact hD.mono hsub

/-- The actual `F`-weighted reduced density of the *shared* quotient
`z=u/f` is integrable in every dimension at least three.  The dominance
`0≤F≤f` gives the same inverse-square pole as for the `f` identity. -/
theorem energyReducedSpatialDensity_shared_quotient_integrableOn_of_taylor_globalC1
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ) (β A B : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hF0 : F 0 = 0) (hβ : 0 < β)
    (hTaylor : RadialOriginTaylorOn f β A B R)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (huC1 : ContDiff ℝ 1 u)
    (hfPos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (hFle : ∀ r : ℝ, 0 < r → r ≤ R →
      0 ≤ F r ∧ F r ≤ f r) :
    IntegrableOn
      (energyReducedSpatialDensity m F
        (fun y : GLEuclidean (m + 3) =>
          (f ‖y‖)⁻¹ • u y))
      (energyPositiveClosedBall (m + 3) R) volume := by
  obtain ⟨δ, Cdf, Cratio, Cp, hδpos, hδR,
    hCdf, hCratio, hCp, hfBounds⟩ :=
    radial_origin_local_flux_bounds_on hR hβ hTaylor
  have hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R) :=
    huC1.continuous.continuousOn
  have hdu : ContinuousOn (fderiv ℝ u)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R) :=
    (huC1.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨Cu, Cg, hCu, hCg, huBounds⟩ :=
    euclideanC1_closedBall_bounds (m + 3) R u hu hdu
  have hInner : IntegrableOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (f ‖y‖)⁻¹ • u y))
        (fun y => ‖(f ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.ball (0 : GLEuclidean (m + 3)) δ) volume := by
    apply shared_quotient_second_density_integrableOn_ball m δ f F u
      Cdf Cratio Cu Cg Cp hF0 hCdf hCratio hCu hCg hCp
    · intro r hrpos hrδ
      have hrR : r < R := lt_of_lt_of_le hrδ hδR
      obtain ⟨hfne, hdf, hratio, hfb⟩ :=
        hfBounds r hrpos hrδ
      exact ⟨(hfC1.differentiable_one r).hasDerivAt,
        hfne, hdf, hratio, hfb⟩
    · intro r hrpos hrδ
      exact hFle r hrpos (le_trans (le_of_lt hrδ) hδR)
    · intro x hx
      have hxR : x ∈ Metric.closedBall
          (0 : GLEuclidean (m + 3)) R := by
        have hxδ : ‖x‖ < δ := by
          simpa only [Metric.mem_ball, dist_zero_right] using hx
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          le_trans (le_of_lt hxδ) hδR
      obtain ⟨hval, hgrad⟩ := huBounds x hxR
      exact ⟨huC1.differentiable_one x, hval, hgrad⟩
    · exact hfC1.continuous.measurable
    · exact hFC1.continuous.measurable
    · exact huC1.continuous.measurable
  have hOuter : ContinuousOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (f ‖y‖)⁻¹ • u y))
        (fun y => ‖(f ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R \
        Metric.ball (0 : GLEuclidean (m + 3)) δ) := by
    apply (shared_quotient_second_density_continuousOn_positiveBall
      m R f F u hfC1 hFC1 huC1 hfPos).mono
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
    have hxδ : δ ≤ ‖x‖ := by
      by_contra hnot
      have hlt : ‖x‖ < δ := lt_of_not_ge hnot
      exact hx.2 (by simpa only [Metric.mem_ball, dist_zero_right] using hlt)
    exact ⟨lt_of_lt_of_le hδpos hxδ, hxR⟩
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun y => (f ‖y‖)⁻¹ • u y
  let D : GLEuclidean (m + 3) → ℝ :=
    singleProfileDensity (m + 3)
      (fun y => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2)
  have hD : IntegrableOn D
      (energyPositiveClosedBall (m + 3) R) volume :=
    integrableOn_positiveBall_of_inner_continuous_outer m R δ D
      (by simpa only [D, z] using hInner)
      (by simpa only [D, z] using hOuter)
  apply hD.congr_fun
  · intro x hx
    have hx0 : x ≠ 0 := by
      intro hzero
      subst x
      simp [energyPositiveClosedBall] at hx
    exact (energyReducedSpatialDensity_eq_singleProfileDensity
      m F z x hx0).symm
  · exact measurableSet_energyPositiveClosedBall (m + 3) R

end

end BrezisOP6
