import BrezisOP6.EnergyQuotientNumeratorOrigin

/-!
# Smoothness of the transformed numerator at the radial origin

For regular vortex profiles, write `p(r)=r H_p(r²)`.  The singular-looking
factor `F(r)/f(r)` then becomes the ordinary smooth function
`H_F(r²)/H_f(r²)`.  This file transfers that observation to the actual
Euclidean transformed numerator, including its removable value at zero.
-/

namespace BrezisOP6

noncomputable section

/-- Positivity of the regular radial profile supplies the nonvanishing
factor required for the smooth quotient.  No separate profile denominator
assumption is needed. -/
theorem radial_factor_ne_zero_on_closedBall
    (n : ℕ) (R : ℝ) (f Hf : ℝ → ℝ) (β : ℝ)
    (hβ : 0 < β) (hHf0 : Hf 0 = β)
    (hf : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r) :
    ∀ x ∈ Metric.closedBall (0 : GLEuclidean n) R,
      Hf (‖x‖ ^ 2) ≠ 0 := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simpa [hHf0] using ne_of_gt hβ
  · have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrle : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hprod : 0 < ‖x‖ * Hf (‖x‖ ^ 2) := by
      rw [← hf ‖x‖ hrpos hrle]
      exact hfpos ‖x‖ hrpos hrle
    exact ne_of_gt ((mul_pos_iff_of_pos_left hrpos).mp hprod)

/-- The canonical representative of `(F/f)u` is `C¹` through the origin
whenever both radial profiles have regular `r H(r²)` factors.  The
nonvanishing condition is needed only on the chosen closed ball. -/
theorem energyQuotientNumerator_contDiffOn_of_radial_factors
    (n : ℕ) (R : ℝ) (f F Hf HF : ℝ → ℝ)
    (α β : ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α)
    (hHfNe : ∀ x ∈ Metric.closedBall (0 : GLEuclidean n) R,
      Hf (‖x‖ ^ 2) ≠ 0)
    (hf : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hF : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hu : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean n) R)) :
    ContDiffOn ℝ 1 (energyQuotientNumerator n f F α β u)
      (Metric.closedBall (0 : GLEuclidean n) R) := by
  let s : Set (GLEuclidean n) := Metric.closedBall 0 R
  let q : GLEuclidean n → ℝ :=
    fun x => HF (‖x‖ ^ 2) / Hf (‖x‖ ^ 2)
  have hsquare : ContDiff ℝ 1
      (fun x : GLEuclidean n => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hnum : ContDiff ℝ 1
      (fun x : GLEuclidean n => HF (‖x‖ ^ 2)) := hHF.comp hsquare
  have hden : ContDiff ℝ 1
      (fun x : GLEuclidean n => Hf (‖x‖ ^ 2)) := hHf.comp hsquare
  have hq : ContDiffOn ℝ 1 q s :=
    hnum.contDiffOn.div hden.contDiffOn hHfNe
  have hqu : ContDiffOn ℝ 1 (fun x => q x • u x) s := hq.smul hu
  apply hqu.congr
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp [energyQuotientNumerator, q, hHF0, hHf0]
  · have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrle : ‖x‖ ≤ R := by
      simpa only [s, Metric.mem_closedBall, dist_zero_right] using hx
    have hfr := hf ‖x‖ hrpos hrle
    have hFr := hF ‖x‖ hrpos hrle
    have hrne : ‖x‖ ≠ 0 := ne_of_gt hrpos
    have hHne : Hf (‖x‖ ^ 2) ≠ 0 := hHfNe x hx
    have hratio : F ‖x‖ / f ‖x‖ =
        HF (‖x‖ ^ 2) / Hf (‖x‖ ^ 2) := by
      rw [hfr, hFr]
      field_simp [hrne, hHne]
    simp [energyQuotientNumerator, hx0, q, hratio]

/-- The ordinary vortex boundary condition makes the quotient field a unit
radial trace on the outer sphere. -/
theorem energyQuotient_unit_trace_of_radial_boundary
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : ℝ → ℝ) (u : GLEuclidean n → GLEuclidean n)
    (hfR : f R ≠ 0)
    (hu : ∀ x : GLEuclidean n, ‖x‖ = R →
      u x = radialVortex n f x) :
    ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      ‖(f ‖energySphereRay n ω R‖)⁻¹ •
        u (energySphereRay n ω R)‖ ^ 2 = 1 := by
  intro ω
  let x := energySphereRay n ω R
  have hxNorm : ‖x‖ = R := energySphereRay_norm n ω R hR.le
  have hradial : radialVortex n f x = f R • (ω : GLEuclidean n) := by
    calc
      radialVortex n f x = (f R / R) • x := by
        simp [radialVortex, hxNorm]
      _ = ((f R / R) * R) • (ω : GLEuclidean n) := by
        simp only [x, energySphereRay, smul_smul]
      _ = f R • (ω : GLEuclidean n) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hR)]
  have hquot : (f ‖x‖)⁻¹ • u x = (ω : GLEuclidean n) := by
    rw [hu x hxNorm, hradial, hxNorm, smul_smul,
      inv_mul_cancel₀ hfR, one_smul]
  rw [show (f ‖energySphereRay n ω R‖)⁻¹ •
      u (energySphereRay n ω R) = (ω : GLEuclidean n) from hquot]
  have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  simp [hω]

/-- The removable `C¹` representative has the entire vortex's outer
boundary trace whenever the original competitor has the finite-ball
vortex trace. -/
theorem energyQuotientNumerator_boundary_trace
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hfR : f R ≠ 0)
    (hu : ∀ x : GLEuclidean n, ‖x‖ = R →
      u x = radialVortex n f x) :
    ∀ x : GLEuclidean n, ‖x‖ = R →
      energyQuotientNumerator n f F α β u x = radialVortex n F x := by
  intro x hxNorm
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    simp at hxNorm
    linarith
  simp only [energyQuotientNumerator, if_neg hx0, hu x hxNorm,
    radialVortex, hxNorm, smul_smul]
  congr 1
  field_simp [hfR, ne_of_gt hR]

end

end BrezisOP6
