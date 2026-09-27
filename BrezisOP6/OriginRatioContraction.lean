import Mathlib

/-!
# Local uniqueness at a regular singular origin by two mean-value steps

This abstract lemma isolates the contraction argument for the normalized
ratio `k=f/F`.  Its coefficient estimate will be supplied by the linear
origin bounds for `F`; no uniqueness of the singular initial-value problem
is assumed in the lemma itself.
-/

namespace BrezisOP6

open Set

noncomputable section

theorem ratio_one_on_small_interval_of_flux_contraction
    {k q A B : ℝ → ℝ} {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hsmall : 6 * C * a ^ 4 < 1)
    (hkcont : ContinuousOn k (Icc (0 : ℝ) a))
    (hqcont : ContinuousOn q (Icc (0 : ℝ) a))
    (hkdiff : ∀ r ∈ Ioo (0 : ℝ) a, DifferentiableAt ℝ k r)
    (hqdiff : ∀ r ∈ Ioo (0 : ℝ) a, DifferentiableAt ℝ q r)
    (hkzero : k 0 = 1) (hqzero : q 0 = 0)
    (hkbounded : ∀ r ∈ Icc (0 : ℝ) a, 0 ≤ k r ∧ k r ≤ 2)
    (hApos : ∀ r ∈ Ioo (0 : ℝ) a, 0 < A r)
    (hBnonneg : ∀ r ∈ Ioo (0 : ℝ) a, 0 ≤ B r)
    (hrelation : ∀ r ∈ Ioo (0 : ℝ) a,
      q r = A r * deriv k r)
    (hflux : ∀ r ∈ Ioo (0 : ℝ) a,
      deriv q r = B r * k r * (k r ^ 2 - 1))
    (hweight : ∀ s ∈ Ioo (0 : ℝ) a,
      ∀ t ∈ Ioo (0 : ℝ) s,
        s * B t ≤ C * s ^ 3 * A s) :
    ∀ r ∈ Icc (0 : ℝ) a, k r = 1 := by
  have hcont : ContinuousOn (fun r : ℝ => |k r - 1|)
      (Icc (0 : ℝ) a) :=
    (hkcont.sub continuousOn_const).abs
  obtain ⟨c, hc, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (show (Icc (0 : ℝ) a).Nonempty from
        ⟨0, ⟨le_rfl, ha.le⟩⟩) hcont
  let M : ℝ := |k c - 1|
  have hMnonneg : 0 ≤ M := abs_nonneg _
  have hbound : ∀ r ∈ Icc (0 : ℝ) a, |k r - 1| ≤ M := by
    intro r hr
    exact hmax hr
  have hMzero : M = 0 := by
    by_contra hMne
    have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hMne)
    have hcpos : 0 < c := by
      rcases eq_or_lt_of_le hc.1 with heq | hlt
      · have : M = 0 := by simp [M, ← heq, hkzero]
        exact (hMne this).elim
      · exact hlt
    have hkcont' : ContinuousOn k (Icc (0 : ℝ) c) :=
      hkcont.mono (by
        intro r hr
        exact ⟨hr.1, hr.2.trans hc.2⟩)
    have hkdiff' : DifferentiableOn ℝ k (Ioo (0 : ℝ) c) := by
      intro r hr
      exact (hkdiff r ⟨hr.1, lt_of_lt_of_le hr.2 hc.2⟩).differentiableWithinAt
    obtain ⟨s, hs, hkslope⟩ :=
      exists_deriv_eq_slope k hcpos hkcont' hkdiff'
    have hsI : s ∈ Ioo (0 : ℝ) a :=
      ⟨hs.1, lt_of_lt_of_le hs.2 hc.2⟩
    have hkeq : k c - 1 = c * deriv k s := by
      have hcnz : c - (0 : ℝ) ≠ 0 := by linarith
      have h := (eq_div_iff hcnz).mp hkslope
      rw [hkzero] at h
      nlinarith [h]
    have hqcont' : ContinuousOn q (Icc (0 : ℝ) s) :=
      hqcont.mono (by
        intro r hr
        exact ⟨hr.1, (hr.2.trans hs.2.le).trans hc.2⟩)
    have hqdiff' : DifferentiableOn ℝ q (Ioo (0 : ℝ) s) := by
      intro r hr
      exact (hqdiff r ⟨hr.1, lt_trans hr.2 hsI.2⟩).differentiableWithinAt
    obtain ⟨t, ht, hqslope⟩ :=
      exists_deriv_eq_slope q hs.1 hqcont' hqdiff'
    have htI : t ∈ Ioo (0 : ℝ) a :=
      ⟨ht.1, lt_trans ht.2 hsI.2⟩
    have hqeq : q s = s * deriv q t := by
      have hsnz : s - (0 : ℝ) ≠ 0 := by
        simpa only [sub_zero] using (ne_of_gt hs.1)
      have h := (eq_div_iff hsnz).mp hqslope
      rw [hqzero] at h
      nlinarith [h]
    have hidentity : A s * (k c - 1) =
        c * (s * B t) * (k t * (k t ^ 2 - 1)) := by
      calc
        A s * (k c - 1) = c * (A s * deriv k s) := by
          rw [hkeq]
          ring
        _ = c * q s := by rw [hrelation s hsI]
        _ = c * (s * deriv q t) := by rw [hqeq]
        _ = c * (s * B t) * (k t * (k t ^ 2 - 1)) := by
          rw [hflux t htI]
          ring
    have hpoly : |k t * (k t ^ 2 - 1)| ≤ 6 * M := by
      have hkt : 0 ≤ k t ∧ k t ≤ 2 :=
        hkbounded t ⟨ht.1.le, htI.2.le⟩
      have hktbound : |k t - 1| ≤ M :=
        hbound t ⟨ht.1.le, htI.2.le⟩
      have hfactor : k t * (k t ^ 2 - 1) =
          k t * (k t + 1) * (k t - 1) := by ring
      rw [hfactor, abs_mul, abs_mul,
        abs_of_nonneg hkt.1,
        abs_of_nonneg (by linarith : 0 ≤ k t + 1)]
      calc
        k t * (k t + 1) * |k t - 1|
            ≤ 2 * 3 * M := by gcongr <;> linarith [hkt.2, hktbound]
        _ = 6 * M := by ring
    have hB : 0 ≤ B t := hBnonneg t htI
    have hA : 0 < A s := hApos s hsI
    have hAbs : A s * M =
        c * (s * B t) * |k t * (k t ^ 2 - 1)| := by
      have habs := congrArg abs hidentity
      simpa only [M, abs_mul, abs_of_pos hA,
        abs_of_pos hcpos, abs_of_pos hs.1,
        abs_of_nonneg hB] using habs
    have hmajor : M ≤ 6 * C * c * s ^ 3 * M := by
      apply (mul_le_mul_iff_of_pos_left hA).mp
      calc
        A s * M = c * (s * B t) * |k t * (k t ^ 2 - 1)| := hAbs
        _ ≤ c * (s * B t) * (6 * M) :=
          mul_le_mul_of_nonneg_left hpoly
            (mul_nonneg hcpos.le (mul_nonneg hs.1.le hB))
        _ ≤ c * (C * s ^ 3 * A s) * (6 * M) := by
          calc
            c * (s * B t) * (6 * M) =
                (c * (6 * M)) * (s * B t) := by ring
            _ ≤ (c * (6 * M)) * (C * s ^ 3 * A s) :=
              mul_le_mul_of_nonneg_left (hweight s hsI t ht)
                (mul_nonneg hcpos.le
                  (mul_nonneg (by norm_num) hMnonneg))
            _ = c * (C * s ^ 3 * A s) * (6 * M) := by ring
        _ = A s * (6 * C * c * s ^ 3 * M) := by ring
    have hca : c ≤ a := hc.2
    have hsa : s ≤ a := hsI.2.le
    have hpower : c * s ^ 3 ≤ a ^ 4 := by
      have hs3 : s ^ 3 ≤ a ^ 3 := by
        gcongr <;> nlinarith [hs.1, hsa]
      calc
        c * s ^ 3 ≤ a * s ^ 3 :=
          mul_le_mul_of_nonneg_right hca (pow_nonneg hs.1.le 3)
        _ ≤ a * a ^ 3 := mul_le_mul_of_nonneg_left hs3 ha.le
        _ = a ^ 4 := by ring
    have hcoeff : 6 * C * c * s ^ 3 < 1 := by
      have hle : 6 * C * c * s ^ 3 ≤ 6 * C * a ^ 4 := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ 6 * C)
          (sub_nonneg.mpr hpower)]
      exact lt_of_le_of_lt hle hsmall
    have hlt : 6 * C * c * s ^ 3 * M < M := by
      have h := mul_lt_mul_of_pos_right hcoeff hMpos
      simpa only [one_mul] using h
    linarith
  intro r hr
  have hzero : |k r - 1| = 0 :=
    le_antisymm (by simpa [hMzero] using hbound r hr) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- The weight estimate needed above follows from the positive profile's
monotonicity and its linear growth bound near the regular origin. -/
theorem radial_ratio_weights_small
    (m : ℕ) (F : ℝ → ℝ) (a L : ℝ)
    (ha : 0 < a) (hL : 0 ≤ L)
    (hFpos : ∀ r ∈ Ioo (0 : ℝ) a, 0 < F r)
    (hFmono : MonotoneOn F (Icc (0 : ℝ) a))
    (hFupper : ∀ r ∈ Ioo (0 : ℝ) a, F r ≤ L * r) :
    ∀ s ∈ Ioo (0 : ℝ) a,
      ∀ t ∈ Ioo (0 : ℝ) s,
        s * (t ^ (m + 2) * F t ^ 4) ≤
          L ^ 2 * s ^ 3 * (s ^ (m + 2) * F s ^ 2) := by
  intro s hs t ht
  have htA : t ∈ Ioo (0 : ℝ) a :=
    ⟨ht.1, lt_trans ht.2 hs.2⟩
  have hFs : 0 < F s := hFpos s hs
  have hFt : 0 < F t := hFpos t htA
  have hFtFs : F t ≤ F s :=
    hFmono ⟨ht.1.le, htA.2.le⟩
      ⟨hs.1.le, hs.2.le⟩ ht.2.le
  have hB : t ^ (m + 2) * F t ^ 4 ≤
      s ^ (m + 2) * F s ^ 4 := by
    have hp : t ^ (m + 2) ≤ s ^ (m + 2) := by
      gcongr <;> nlinarith [ht.1, ht.2]
    have hF4 : F t ^ 4 ≤ F s ^ 4 := by gcongr
    exact mul_le_mul hp hF4 (pow_nonneg hFt.le 4)
      (pow_nonneg hs.1.le _)
  have hFs2 : F s ^ 2 ≤ L ^ 2 * s ^ 2 := by
    have hLs : 0 ≤ L * s := mul_nonneg hL hs.1.le
    nlinarith [hFupper s hs]
  calc
    s * (t ^ (m + 2) * F t ^ 4)
        ≤ s * (s ^ (m + 2) * F s ^ 4) :=
          mul_le_mul_of_nonneg_left hB hs.1.le
    _ = (s * (s ^ (m + 2) * F s ^ 2)) * F s ^ 2 := by ring
    _ ≤ (s * (s ^ (m + 2) * F s ^ 2)) *
        (L ^ 2 * s ^ 2) := by
          exact mul_le_mul_of_nonneg_left hFs2
            (mul_nonneg hs.1.le
              (mul_nonneg (pow_nonneg hs.1.le _) (sq_nonneg _)))
    _ = L ^ 2 * s ^ 3 * (s ^ (m + 2) * F s ^ 2) := by ring

end

end BrezisOP6
