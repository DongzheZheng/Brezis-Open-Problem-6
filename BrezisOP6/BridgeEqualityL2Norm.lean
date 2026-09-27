import BrezisOP6.BridgeEqualityRadial

/-!
# A sphere-valued L² norm budget

If the mean-zero part of each target coordinate is fixed and the total
L² norm stays fixed, no nonzero constant spherical mode can be added.
This is the final algebraic step in equality rigidity; it does not use an
equality-case classification for the sphere Poincaré inequality.
-/

namespace BrezisOP6

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem meanZero_traces_equal_of_fixed_total_norm
    (n : ℕ) (e : H) (v w : Fin n → H) (c : Fin n → ℝ)
    (he : ‖e‖ = 1)
    (hw : ∀ i, inner ℝ (w i) e = 0)
    (hpart : ∀ i, v i - c i • e = w i)
    (hnorm : (∑ i : Fin n, ‖v i‖ ^ 2) =
      ∑ i : Fin n, ‖w i‖ ^ 2) :
    ∀ i : Fin n, v i = w i := by
  have hp (i : Fin n) :
      ‖v i‖ ^ 2 = c i ^ 2 + ‖w i‖ ^ 2 := by
    have horth : inner ℝ (v i - c i • e) e = 0 := by
      rw [hpart i]
      exact hw i
    simpa only [hpart i] using
      (norm_sq_eq_mean_sq_add_orthogonal e (v i) (c i) he horth)
  have hbudget : (∑ i : Fin n, c i ^ 2) = 0 := by
    have hs : (∑ i : Fin n, ‖v i‖ ^ 2) =
        (∑ i : Fin n, c i ^ 2) +
          (∑ i : Fin n, ‖w i‖ ^ 2) := by
      simp_rw [hp]
      rw [Finset.sum_add_distrib]
    linarith
  intro i
  have hle : c i ^ 2 ≤ ∑ j : Fin n, c j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (c j))
      (Finset.mem_univ i)
  have hciSq : c i ^ 2 = 0 := by
    nlinarith [sq_nonneg (c i)]
  have hci : c i = 0 := by nlinarith
  calc
    v i = (v i - c i • e) + c i • e := by abel
    _ = w i := by rw [hpart i, hci]; simp

end

end BrezisOP6
