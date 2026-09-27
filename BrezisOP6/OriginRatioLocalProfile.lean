import BrezisOP6.OriginRatioContraction
import BrezisOP6.ProfileBoundsAssembly

/-!
# Regular-origin uniqueness on a small interval for actual GL profiles

The abstract two-MVT contraction is now instantiated with the weighted
Wronskian of two solutions of the radial Ginzburg--Landau equation.  The
remaining small-radius linear bound and bounded-ratio hypotheses follow
from the previously verified Taylor limits and continuity at zero; they
are kept explicit here while that last packaging step is performed.
-/

namespace BrezisOP6

open Set
open scoped Topology

noncomputable section

/-- Two-sided linear control of the positive profile gives exactly the
weighted estimate used in the two-MVT contraction.  Monotonicity of `F`
is unnecessary. -/
theorem radial_ratio_weights_small_of_linear_bounds
    (m : ℕ) (F : ℝ → ℝ) (a c L C : ℝ)
    (hc : 0 < c) (hL : 0 ≤ L)
    (hCL : L ^ 4 ≤ C * c ^ 2)
    (hFlower : ∀ r ∈ Ioo (0 : ℝ) a, c * r ≤ F r)
    (hFupper : ∀ r ∈ Ioo (0 : ℝ) a, F r ≤ L * r) :
    ∀ s ∈ Ioo (0 : ℝ) a,
      ∀ t ∈ Ioo (0 : ℝ) s,
        s * (t ^ (m + 2) * F t ^ 4) ≤
          C * s ^ 3 * (s ^ (m + 2) * F s ^ 2) := by
  intro s hs t ht
  have htA : t ∈ Ioo (0 : ℝ) a :=
    ⟨ht.1, lt_trans ht.2 hs.2⟩
  have hFs : 0 ≤ F s := le_trans (mul_nonneg hc.le hs.1.le) (hFlower s hs)
  have hFt : 0 ≤ F t := le_trans (mul_nonneg hc.le ht.1.le) (hFlower t htA)
  have hp : t ^ (m + 2) ≤ s ^ (m + 2) := by
    gcongr <;> nlinarith [ht.1, ht.2]
  have hFts : F t ≤ L * s := by
    calc
      F t ≤ L * t := hFupper t htA
      _ ≤ L * s := mul_le_mul_of_nonneg_left ht.2.le hL
  have hFt4 : F t ^ 4 ≤ L ^ 4 * s ^ 4 := by
    calc
      F t ^ 4 ≤ (L * s) ^ 4 := by gcongr
      _ = L ^ 4 * s ^ 4 := by ring
  have hFs2 : c ^ 2 * s ^ 2 ≤ F s ^ 2 := by
    calc
      c ^ 2 * s ^ 2 = (c * s) ^ 2 := by ring
      _ ≤ F s ^ 2 := by
        gcongr <;> nlinarith [hFlower s hs, mul_pos hc hs.1]
  have hCLs : L ^ 4 * s ^ 2 ≤ C * F s ^ 2 := by
    have hC : 0 ≤ C := by
      have hcsq : 0 < c ^ 2 := sq_pos_of_pos hc
      nlinarith [sq_nonneg L, hCL]
    calc
      L ^ 4 * s ^ 2 ≤ (C * c ^ 2) * s ^ 2 :=
        mul_le_mul_of_nonneg_right hCL (sq_nonneg s)
      _ = C * (c ^ 2 * s ^ 2) := by ring
      _ ≤ C * F s ^ 2 := mul_le_mul_of_nonneg_left hFs2 hC
  have hB : t ^ (m + 2) * F t ^ 4 ≤
      s ^ (m + 2) * (L ^ 4 * s ^ 4) := by
    exact mul_le_mul hp hFt4 (pow_nonneg hFt 4)
      (pow_nonneg hs.1.le _)
  calc
    s * (t ^ (m + 2) * F t ^ 4)
        ≤ s * (s ^ (m + 2) * (L ^ 4 * s ^ 4)) :=
          mul_le_mul_of_nonneg_left hB hs.1.le
    _ = (s ^ (m + 2) * s ^ 3) * (L ^ 4 * s ^ 2) := by ring
    _ ≤ (s ^ (m + 2) * s ^ 3) * (C * F s ^ 2) :=
          mul_le_mul_of_nonneg_left hCLs
            (mul_nonneg (pow_nonneg hs.1.le _) (pow_nonneg hs.1.le 3))
    _ = C * s ^ 3 * (s ^ (m + 2) * F s ^ 2) := by ring

theorem profile_ratio_one_on_small_interval
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (a c L C : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hCL : L ^ 4 ≤ C * c ^ 2)
    (hsmall : 6 * C * a ^ 4 < 1)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) a, 0 < F r)
    (hFlower : ∀ r ∈ Ioo (0 : ℝ) a, c * r ≤ F r)
    (hFupper : ∀ r ∈ Ioo (0 : ℝ) a, F r ≤ L * r)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) a))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) a,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkzero : k₀ 0 = 1)
    (hkbounded : ∀ r ∈ Icc (0 : ℝ) a, 0 ≤ k₀ r ∧ k₀ r ≤ 2)
    (hfluxcont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) a))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) a,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) a,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) a,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) a,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r)) :
    ∀ r ∈ Icc (0 : ℝ) a, k₀ r = 1 := by
  let A : ℝ → ℝ := fun r => r ^ (m + 2) * F r ^ 2
  let B : ℝ → ℝ := fun r => r ^ (m + 2) * F r ^ 4
  let q : ℝ → ℝ := ratioFlux (m + 2) f F
  have hpoint : ∀ r ∈ Ioc (0 : ℝ) a,
      k₀ r = profileK f F r := by
    intro r hr
    exact (hkevent r hr).eq_of_nhds
  have hkdiff : ∀ r ∈ Ioo (0 : ℝ) a,
      DifferentiableAt ℝ k₀ r := by
    intro r hr
    have hrC : r ∈ Ioc (0 : ℝ) a := ⟨hr.1, hr.2.le⟩
    have hdiv : DifferentiableAt ℝ (profileK f F) r :=
      (hfDiff r).div (hFDiff r) (ne_of_gt (hFpos r hrC))
    exact hdiv.congr_of_eventuallyEq (hkevent r hrC)
  have hApos : ∀ r ∈ Ioo (0 : ℝ) a, 0 < A r := by
    intro r hr
    exact mul_pos (pow_pos hr.1 _)
      (sq_pos_of_pos (hFpos r ⟨hr.1, hr.2.le⟩))
  have hBnonneg : ∀ r ∈ Ioo (0 : ℝ) a, 0 ≤ B r := by
    intro r hr
    exact le_of_lt (mul_pos (pow_pos hr.1 _)
      (pow_pos (hFpos r ⟨hr.1, hr.2.le⟩) _))
  have hrelation : ∀ r ∈ Ioo (0 : ℝ) a,
      q r = A r * deriv k₀ r := by
    intro r hr
    have hrC : r ∈ Ioc (0 : ℝ) a := ⟨hr.1, hr.2.le⟩
    have hFlux := ratioFlux_eq_ratio (m + 2)
      (hfDiff r) (hFDiff r) (ne_of_gt (hFpos r hrC))
    have hderiv : deriv k₀ r =
        deriv (fun t => f t / F t) r := by
      simpa only [profileK] using (hkevent r hrC).deriv_eq
    simpa only [q, A, hderiv] using hFlux
  have hfluxDeriv : ∀ r ∈ Ioo (0 : ℝ) a,
      HasDerivAt q
        (r ^ (m + 2) * F r * f r * (f r ^ 2 - F r ^ 2)) r := by
    intro r hr
    have hODEf := radialODEAt_divided_for_profile_flux m f r (f₂ r)
      hr.1 (hode_f r hr)
    have hODEF := radialODEAt_divided_for_profile_flux m F r (F₂ r)
      hr.1 (hode_F r hr)
    have hFlux := ratioFlux_hasDerivAt (m + 1) (ne_of_gt hr.1)
      (hfDiff r).hasDerivAt (hFDiff r).hasDerivAt
      (hdf r hr) (hdF r hr) hODEf hODEF
    simpa only [q, show (m + 1) + 1 = m + 2 by omega] using hFlux
  have hqdiff : ∀ r ∈ Ioo (0 : ℝ) a,
      DifferentiableAt ℝ q r := by
    intro r hr
    exact (hfluxDeriv r hr).differentiableAt
  have hflux : ∀ r ∈ Ioo (0 : ℝ) a,
      deriv q r = B r * k₀ r * (k₀ r ^ 2 - 1) := by
    intro r hr
    have hrC : r ∈ Ioc (0 : ℝ) a := ⟨hr.1, hr.2.le⟩
    rw [(hfluxDeriv r hr).deriv, hpoint r hrC]
    unfold B profileK
    field_simp [ne_of_gt (hFpos r hrC)]
  have hweight : ∀ s ∈ Ioo (0 : ℝ) a,
      ∀ t ∈ Ioo (0 : ℝ) s,
        s * B t ≤ C * s ^ 3 * A s := by
    intro s hs t ht
    exact radial_ratio_weights_small_of_linear_bounds
      m F a c L C hc hL hCL hFlower hFupper s hs t ht
  exact ratio_one_on_small_interval_of_flux_contraction
    ha hC hsmall hkcont hfluxcont hkdiff hqdiff
    hkzero (by simp [q, ratioFlux]) hkbounded hApos hBnonneg
    hrelation hflux hweight

end

end BrezisOP6
