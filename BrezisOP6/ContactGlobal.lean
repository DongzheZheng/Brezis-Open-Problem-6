import BrezisOP6.ContactFormation
import BrezisOP6.GlobalContact

/-!
# Global positivity of the Picone residual under the profile bounds

The contact polynomial and first-contact calculus are assembled into an
interval theorem.  Its hypotheses isolate the two remaining analytic inputs:
positivity near the origin and the auxiliary bounds on the profile flow.
The resulting conclusion is strict positivity of `S` on the whole interval.
-/

namespace BrezisOP6

noncomputable section

/-- A profile trajectory satisfying the verified contact-domain bounds has
strictly positive Picone residual on every interval starting where `S>0`.
The variable `s` is logarithmic radius; the five derivative hypotheses are
the actual flow equations. -/
theorem residualAlong_positive_on_interval
    {r t y k eta : ℝ → ℝ} {a b n : ℝ}
    (hcont : ContinuousOn (residualAlong r t y k eta) (Set.Icc a b))
    (hSa : 0 < residualAlong r t y k eta a)
    (hn : 2 < n)
    (hr : ∀ s, a < s → s ≤ b → HasDerivAt r (r s) s)
    (ht : ∀ s, a < s → s ≤ b →
      HasDerivAt t (t s * (2 - y s)) s)
    (hy : ∀ s, a < s → s ≤ b →
      HasDerivAt y (y s ^ 2 - n * y s + r s ^ 2 - t s ^ 2) s)
    (hk : ∀ s, a < s → s ≤ b →
      HasDerivAt k ((k s ^ 2 - 1) * eta s) s)
    (heta : ∀ s, a < s → s ≤ b →
      HasDerivAt eta
        (k s * t s ^ 2 - (n - 2 * y s) * eta s -
          2 * k s * eta s ^ 2) s)
    (hbounds : ∀ s, a < s → s ≤ b →
      ∃ X q : ℝ,
        0 < k s ^ 2 - 1 ∧
        0 < y s ∧ y s < 1 ∧
        0 < k s ∧ 0 < eta s ∧
        eta s ^ 2 < r s ^ 2 / 2 ∧
        0 < X ∧ X < 1 ∧
        (k s ^ 2 - 1) * eta s = k s * X * y s ∧
        y s ≤ q ∧ t s ^ 2 = r s ^ 2 * q) :
    ∀ s ∈ Set.Icc a b, 0 < residualAlong r t y k eta s := by
  apply positive_on_Icc_of_positive_derivative_at_zeros_continuousOn hcont hSa
  intro s has hsb hzero
  obtain ⟨X, q, hM, hy0, hy1, hk0, heta0, hetaSmall,
    hX0, hX1, hchi, hq, htrel⟩ := hbounds s has hsb
  have hD := residualAlong_hasDerivAt_of_flow
    (hr s has hsb) (ht s has hsb) (hy s has hsb)
    (hk s has hsb) (heta s has hsb)
  have hpos := residualAlong_deriv_pos_at_zero
    (hr s has hsb) (ht s has hsb) (hy s has hsb)
    (hk s has hsb) (heta s has hsb)
    hn hzero hM hy0 hy1 hk0 heta0 hetaSmall
    hX0 hX1 hchi hq htrel
  exact ⟨_, hD, by simpa only [hD.deriv] using hpos⟩

end

end BrezisOP6
