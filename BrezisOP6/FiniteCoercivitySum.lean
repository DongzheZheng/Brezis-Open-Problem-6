import Mathlib

/-!
# Summing finitely many quantitative mode estimates

The analytic bridge is proved one target coordinate at a time.  This
elementary lemma produces one strictly positive constant for the entire
vector field and is independent of the harmonic or PDE setup.
-/

namespace BrezisOP6

theorem finite_coercivity_sum
    (n : ℕ) (hn : 0 < n) (A Q : Fin n → ℝ)
    (hQ : ∀ k, 0 ≤ Q k)
    (hA : ∀ k, ∃ C : ℝ, 0 < C ∧ A k ≤ C * Q k) :
    ∃ C : ℝ, 0 < C ∧
      (∑ k : Fin n, A k) ≤ C * (∑ k : Fin n, Q k) := by
  choose c hcPos hcBound using hA
  let C : ℝ := ∑ k : Fin n, c k
  have hCpos : 0 < C := by
    exact Finset.sum_pos (fun k _ => hcPos k)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hCk (k : Fin n) : c k ≤ C :=
    Finset.single_le_sum (fun j _ => (hcPos j).le)
      (Finset.mem_univ k)
  refine ⟨C, hCpos, ?_⟩
  calc
    (∑ k : Fin n, A k) ≤ ∑ k : Fin n, c k * Q k :=
      Finset.sum_le_sum (fun k _ => hcBound k)
    _ ≤ ∑ k : Fin n, C * Q k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hCk k) (hQ k)
    _ = C * (∑ k : Fin n, Q k) := by
      rw [Finset.mul_sum]

end BrezisOP6
