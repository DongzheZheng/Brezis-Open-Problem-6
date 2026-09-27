import BrezisOP6.PositiveRadiusDifference

/-!
# Positive-radius uniqueness for the linear difference system

The difference of two radial profiles is governed by a first-order linear
system.  This module applies mathlib's ODE uniqueness theorem to that
system.  The only quantitative data are bounds on its two coefficients
over a compact interval away from radius zero.
-/

namespace BrezisOP6

open Set

noncomputable section

def radialDifferencePairField (A B : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, A * x.1 + B * x.2)

theorem radialDifferencePairField_lipschitz
    (A B C : ℝ) (hC : 0 ≤ C)
    (hA : |A| ≤ C) (hB : |B| ≤ C) :
    LipschitzWith (1 + 2 * C).toNNReal
      (radialDifferencePairField A B) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  let M := ‖x - y‖
  have hM : 0 ≤ M := norm_nonneg _
  have hfirst : ‖x.1 - y.1‖ ≤ M := by
    simpa only [M, Prod.fst_sub] using (norm_fst_le (x - y))
  have hsecond : ‖x.2 - y.2‖ ≤ M := by
    simpa only [M, Prod.snd_sub] using (norm_snd_le (x - y))
  have hcoeff : |A| + |B| ≤ 2 * C := by linarith
  have hlin :
      ‖A * (x.1 - y.1) + B * (x.2 - y.2)‖ ≤ 2 * C * M := by
    calc
      _ ≤ ‖A * (x.1 - y.1)‖ + ‖B * (x.2 - y.2)‖ := norm_add_le _ _
      _ = |A| * ‖x.1 - y.1‖ + |B| * ‖x.2 - y.2‖ := by
        simp [norm_mul, Real.norm_eq_abs]
      _ ≤ |A| * M + |B| * M := by
        gcongr
      _ = (|A| + |B|) * M := by ring
      _ ≤ 2 * C * M := mul_le_mul_of_nonneg_right hcoeff hM
  have hfactor : 1 ≤ 1 + 2 * C := by linarith
  have hfactor2 : 2 * C ≤ 1 + 2 * C := by linarith
  simp only [dist_eq_norm]
  have hfield :
      radialDifferencePairField A B x -
        radialDifferencePairField A B y =
        (x.2 - y.2,
          A * (x.1 - y.1) + B * (x.2 - y.2)) := by
    ext <;> dsimp [radialDifferencePairField] <;> ring
  rw [hfield]
  change ‖(x.2 - y.2,
    A * (x.1 - y.1) + B * (x.2 - y.2))‖ ≤
      (1 + 2 * C) * M
  rw [Prod.norm_mk]
  apply max_le
  · exact hsecond.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hM])
  · exact hlin.trans (mul_le_mul_of_nonneg_right hfactor2 hM)

theorem linear_difference_pair_zero_on_open_interval
    (A B d e : ℝ → ℝ) (a b s C : ℝ)
    (ha : a < s) (hb : s < b) (hC : 0 ≤ C)
    (hA : ∀ t ∈ Ioo a b, |A t| ≤ C)
    (hB : ∀ t ∈ Ioo a b, |B t| ≤ C)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt d (e t) t)
    (he : ∀ t ∈ Ioo a b,
      HasDerivAt e (A t * d t + B t * e t) t)
    (hds : d s = 0) (hes : e s = 0) :
    ∀ t ∈ Ioo a b, d t = 0 ∧ e t = 0 := by
  let X : ℝ → ℝ × ℝ := fun t => (d t, e t)
  let Z : ℝ → ℝ × ℝ := fun _ => (0, 0)
  let v : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
    fun t => radialDifferencePairField (A t) (B t)
  have hv : ∀ t ∈ Ioo a b,
      LipschitzOnWith (1 + 2 * C).toNNReal (v t) (Set.univ) := by
    intro t ht
    exact (radialDifferencePairField_lipschitz
      (A t) (B t) C hC (hA t ht) (hB t ht)).lipschitzOnWith
  have hX : ∀ t ∈ Ioo a b,
      HasDerivAt X (v t (X t)) t ∧ X t ∈ Set.univ := by
    intro t ht
    constructor
    · simpa only [X, v, radialDifferencePairField] using
        (hd t ht).prodMk (he t ht)
    · trivial
  have hZ : ∀ t ∈ Ioo a b,
      HasDerivAt Z (v t (Z t)) t ∧ Z t ∈ Set.univ := by
    intro t _
    constructor
    · simpa [Z, v, radialDifferencePairField] using
        (hasDerivAt_const t (0 : ℝ × ℝ))
    · trivial
  have hEq : Set.EqOn X Z (Ioo a b) :=
    ODE_solution_unique_of_mem_Ioo hv ⟨ha, hb⟩ hX hZ
      (by simp [X, Z, hds, hes])
  intro t ht
  have h := hEq ht
  constructor
  · simpa [X, Z] using congrArg Prod.fst h
  · simpa [X, Z] using congrArg Prod.snd h

/-- On a compact interval, continuity supplies the common Lipschitz bound
required above.  This is the standard positive-radius IVP uniqueness
statement for the linear difference system. -/
theorem linear_difference_pair_zero_of_continuous_coefficients
    (A B d e : ℝ → ℝ) (a b s : ℝ)
    (ha : a < s) (hb : s < b)
    (hAcont : ContinuousOn A (Icc a b))
    (hBcont : ContinuousOn B (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt d (e t) t)
    (he : ∀ t ∈ Ioo a b,
      HasDerivAt e (A t * d t + B t * e t) t)
    (hds : d s = 0) (hes : e s = 0) :
    ∀ t ∈ Ioo a b, d t = 0 ∧ e t = 0 := by
  obtain ⟨CA, hCA⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hAcont
  obtain ⟨CB, hCB⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hBcont
  let C := max 0 (max CA CB)
  have hC : 0 ≤ C := le_max_left _ _
  have hA (t : ℝ) (ht : t ∈ Ioo a b) : |A t| ≤ C := by
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have h := hCA t ht'
    simpa only [Real.norm_eq_abs] using
      h.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  have hB (t : ℝ) (ht : t ∈ Ioo a b) : |B t| ≤ C := by
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have h := hCB t ht'
    simpa only [Real.norm_eq_abs] using
      h.trans (le_trans (le_max_right _ _) (le_max_right _ _))
  exact linear_difference_pair_zero_on_open_interval
    A B d e a b s C ha hb hC hA hB hd he hds hes

end

end BrezisOP6
