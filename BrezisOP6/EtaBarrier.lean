import BrezisOP6.FirstContact

/-!
# The strict barrier for the normalized profile-growth variable

At a first contact with `η = r / √2`, the flow equation has a strictly
negative right-hand side.  This file isolates the exact pointwise algebra;
the assumptions on `F`, `y`, `k`, and the dimension are written explicitly.
-/

namespace BrezisOP6

noncomputable section

/-- At the candidate barrier contact, the two quadratic `k`-terms in the
`η`-flow combine to `-k r²(1-F²)`.  Both remaining terms are negative. -/
theorem eta_flow_negative_at_barrier {ν r k F y η t η₁ : ℝ}
    (hr : 0 < r) (hk : 0 < k)
    (hF0 : 0 < F) (hF1 : F < 1)
    (hy1 : y < 1) (hν : 2 ≤ ν)
    (ht : t = r * F) (hcontact : η = r / Real.sqrt 2)
    (hflow : r * η₁ = k * t ^ 2 - (ν - 2 * y) * η - 2 * k * η ^ 2) :
    r * η₁ < 0 := by
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hroot : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have heta : 0 < η := by rw [hcontact]; exact div_pos hr hrootpos
  have hFbracket : 0 < 1 - F ^ 2 := by nlinarith
  have hνy : 0 < ν - 2 * y := by linarith
  have htwoeta : 2 * η ^ 2 = r ^ 2 := by
    rw [hcontact]
    calc
      2 * (r / Real.sqrt 2) ^ 2 = r ^ 2 * (2 / (Real.sqrt 2) ^ 2) := by ring
      _ = r ^ 2 := by rw [hroot]; ring
  have hrewrite :
      r * η₁ = -k * r ^ 2 * (1 - F ^ 2) - (ν - 2 * y) * η := by
    calc
      r * η₁ = k * t ^ 2 - (ν - 2 * y) * η - 2 * k * η ^ 2 := hflow
      _ = -k * r ^ 2 * (1 - F ^ 2) - (ν - 2 * y) * η := by
        rw [ht]
        linear_combination -k * htwoeta
  rw [hrewrite]
  have hfirst : 0 < k * r ^ 2 * (1 - F ^ 2) := by positivity
  have hsecond : 0 < (ν - 2 * y) * η := mul_pos hνy heta
  linarith

/-- The paper's integer dimension assumption `n ≥ 2` implies the real
dimension hypothesis in `eta_flow_negative_at_barrier`. -/
theorem eta_flow_negative_at_barrier_nat {n : ℕ} {r k F y η t η₁ : ℝ}
    (hn : 2 ≤ n) (hr : 0 < r) (hk : 0 < k)
    (hF0 : 0 < F) (hF1 : F < 1)
    (hy1 : y < 1)
    (ht : t = r * F) (hcontact : η = r / Real.sqrt 2)
    (hflow : r * η₁ = k * t ^ 2 - ((n : ℝ) - 2 * y) * η -
      2 * k * η ^ 2) : r * η₁ < 0 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact eta_flow_negative_at_barrier hr hk hF0 hF1 hy1 hnreal
    ht hcontact hflow

/-- Full first-contact contradiction for the barrier `η(r) < r/√2`.
The left-hand interval is kept explicit, so this theorem can be applied at
the first putative contact after the origin expansion establishes the
barrier locally. -/
theorem eta_no_first_contact {ν a r k F y t η₁ : ℝ}
    {η : ℝ → ℝ}
    (ha : a < r) (hr : 0 < r)
    (hleft : ∀ x, a < x → x < r → η x < x / Real.sqrt 2)
    (hcontact : η r = r / Real.sqrt 2)
    (hderiv : HasDerivAt η η₁ r)
    (hk : 0 < k) (hF0 : 0 < F) (hF1 : F < 1)
    (hy1 : y < 1) (hν : 2 ≤ ν)
    (ht : t = r * F)
    (hflow : r * η₁ = k * t ^ 2 - (ν - 2 * y) * η r -
      2 * k * (η r) ^ 2) : False := by
  let S : ℝ → ℝ := fun x => x / Real.sqrt 2 - η x
  have hleftS : ∀ x, a < x → x < r → S r ≤ S x := by
    intro x hax hxr
    dsimp [S]
    rw [hcontact]
    linarith [hleft x hax hxr]
  have hlinear : HasDerivAt (fun x : ℝ => x / Real.sqrt 2)
      (1 / Real.sqrt 2) r := by
    simpa using (hasDerivAt_id r).div_const (Real.sqrt 2)
  have hderS : HasDerivAt S (1 / Real.sqrt 2 - η₁) r :=
    hlinear.sub hderiv
  have hsign : 1 / Real.sqrt 2 - η₁ ≤ 0 :=
    deriv_nonpos_at_first_contact ha hleftS hderS
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have heta₁ : 0 < η₁ := by
    have hone : 0 < 1 / Real.sqrt 2 := div_pos (by norm_num) hrootpos
    linarith
  have hpos : 0 < r * η₁ := mul_pos hr heta₁
  have hneg : r * η₁ < 0 :=
    eta_flow_negative_at_barrier hr hk hF0 hF1 hy1 hν
      ht hcontact hflow
  linarith

end

end BrezisOP6
