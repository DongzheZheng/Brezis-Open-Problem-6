import Mathlib
import BrezisOP6.Polynomial

/-!
# The contact identity for the higher-dimensional OP6 argument

This module verifies the polynomial calculation at a first zero of the
Picone residual. The real parameter n permits a stronger algebraic
statement than the paper's integer-dimensional specialization.
-/

namespace BrezisOP6

noncomputable section

/-- The Picone residual \(S=r^2+Mt^2-4y-2y^2-\eta^2\). -/
def contactResidual (r t y M eta : ℝ) : ℝ :=
  r ^ 2 + M * t ^ 2 - 4 * y - 2 * y ^ 2 - eta ^ 2

/-- The positive factor multiplying \(n-2\) at a first contact. -/
def contactGain (eta y : ℝ) : ℝ :=
  eta ^ 2 + 2 * y ^ 2 + 2 * y

/-- The coefficient of \(t^2\) in the dimension-independent contact term. -/
def contactTCoeff (y k M eta : ℝ) : ℝ :=
  k * eta * (M - 1) + (M + 2) * y + 3 * M + 2

/-- The dimension-independent part of the contact expression. -/
def contactCore (t y k M eta : ℝ) : ℝ :=
  2 * k * eta ^ 3 + (1 - 4 * y) * eta ^ 2 -
    6 * y ^ 3 - 8 * y ^ 2 + contactTCoeff y k M eta * t ^ 2

/-- The expression for \(rS'(r)/2\) obtained directly from the five
first-order profile equations, before imposing \(S=0\). -/
def contactDrift (n r t y k M eta : ℝ) : ℝ :=
  r ^ 2 + M * t ^ 2 * (k * eta + 2 - y) -
    2 * (1 + y) * (y ^ 2 - n * y + r ^ 2 - t ^ 2) -
    eta * (k * t ^ 2 - (n - 2 * y) * eta - 2 * k * eta ^ 2)

/-- The unrestricted polynomial identity. The last term vanishes exactly
at a contact point. This is equation (5.1) of the paper before imposing
\(S=0\). -/
theorem contactDrift_decomposition (n r t y k M eta : ℝ) :
    contactDrift n r t y k M eta =
      contactCore t y k M eta + (n - 2) * contactGain eta y -
        (1 + 2 * y) * contactResidual r t y M eta := by
  unfold contactDrift contactCore contactTCoeff contactGain contactResidual
  ring

/-- Chain-rule link to the radial flow. The independent variable is
\(s=\log r\); hence the paper's operator \(r\,d/dr\) is \(d/ds\).
The hypotheses are exactly the components of equation (3.5) needed for
the derivative of \(S\), together with \(dr/ds=r\). -/
theorem contactResidual_hasDerivAt_logRadius
    {r t y M eta : ℝ → ℝ} {s n k : ℝ}
    (hr : HasDerivAt r (r s) s)
    (ht : HasDerivAt t (t s * (2 - y s)) s)
    (hy : HasDerivAt y (y s ^ 2 - n * y s + r s ^ 2 - t s ^ 2) s)
    (hM : HasDerivAt M (2 * k * M s * eta s) s)
    (heta : HasDerivAt eta
      (k * t s ^ 2 - (n - 2 * y s) * eta s -
        2 * k * eta s ^ 2) s) :
    HasDerivAt
      (fun z => contactResidual (r z) (t z) (y z) (M z) (eta z))
      (2 * contactDrift n (r s) (t s) (y s) k (M s) (eta s)) s := by
  have hcalc :=
    ((((hr.pow 2).add (hM.mul (ht.pow 2))).sub (hy.const_mul 4)).sub
      ((hy.pow 2).const_mul 2)).sub (heta.pow 2)
  convert hcalc using 1
  · dsimp
    unfold contactDrift
    ring

/-- Equation (5.1): at a zero of \(S\), the derivative splits into the
two-dimensional contact expression plus the higher-dimensional gain. -/
theorem contactDrift_at_zero {n r t y k M eta : ℝ}
    (hS : contactResidual r t y M eta = 0) :
    contactDrift n r t y k M eta =
      contactCore t y k M eta + (n - 2) * contactGain eta y := by
  rw [contactDrift_decomposition, hS]
  ring

/-- The gain itself is strictly positive whenever \(y>0\). No condition on
\(\eta\) is needed because its contribution is a square. -/
theorem contactGain_pos {eta y : ℝ} (hy : 0 < y) :
    0 < contactGain eta y := by
  unfold contactGain
  nlinarith [sq_nonneg eta, sq_nonneg y]

/-- The extra contact term is strictly positive for every real \(n>2\).
In particular this covers every integer dimension \(n\ge3\). -/
theorem contactDimensionalIncrement_pos {n eta y : ℝ}
    (hn : 2 < n) (hy : 0 < y) :
    0 < (n - 2) * contactGain eta y :=
  mul_pos (sub_pos.mpr hn) (contactGain_pos hy)

/-- If the dimension-independent contact term is nonnegative, the full
derivative expression is strictly positive at a zero of \(S\). -/
theorem contactDrift_pos_at_zero {n r t y k M eta : ℝ}
    (hn : 2 < n) (hy : 0 < y)
    (hS : contactResidual r t y M eta = 0)
    (hcore : 0 ≤ contactCore t y k M eta) :
    0 < contactDrift n r t y k M eta := by
  rw [contactDrift_at_zero hS]
  have hgain := contactDimensionalIncrement_pos (eta := eta) hn hy
  linarith

/-- At a contact, \(r^2+Mt^2=\eta^2+2y(y+2)\). -/
theorem contact_radius_relation {r t y M eta : ℝ}
    (hS : contactResidual r t y M eta = 0) :
    r ^ 2 + M * t ^ 2 = eta ^ 2 + 2 * y * (y + 2) := by
  unfold contactResidual at hS
  nlinarith

/-- The comparison \(F^2\ge y\), written as \(q\ge y\) and
\(t^2=r^2q\), gives the lower bound for \(t^2\) at a contact. -/
theorem contact_t_sq_lower {r t y M eta q : ℝ}
    (hS : contactResidual r t y M eta = 0)
    (hq : y ≤ q) (ht : t ^ 2 = r ^ 2 * q) :
    y * (eta ^ 2 + 2 * y * (y + 2)) ≤
      (1 + M * y) * t ^ 2 := by
  have hr := contact_radius_relation hS
  have hry := congrArg (fun z : ℝ => y * z) hr
  have hnonneg : 0 ≤ r ^ 2 * (q - y) :=
    mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hq)
  nlinarith

/-- The coefficient \(C_t\) is positive on the auxiliary contact domain.
The proof uses only the weaker bound \(\eta^2<r^2/2\). -/
theorem contactTCoeff_pos {r t y k M eta : ℝ}
    (hS : contactResidual r t y M eta = 0)
    (hM : 0 < M) (hy : 0 < y) (hk : 0 < k) (heta : 0 < eta)
    (hk2 : k ^ 2 = 1 + M)
    (heta2 : eta ^ 2 < r ^ 2 / 2) :
    0 < contactTCoeff y k M eta := by
  have hr := contact_radius_relation hS
  by_cases hM1 : 1 ≤ M
  · have hfirst : 0 ≤ k * eta * (M - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt hk) (le_of_lt heta))
        (sub_nonneg.mpr hM1)
    have hsecond : 0 ≤ (M + 2) * y := by positivity
    unfold contactTCoeff
    nlinarith
  · have hMlt : M < 1 := lt_of_not_ge hM1
    have hMt : 0 ≤ M * t ^ 2 := mul_nonneg (le_of_lt hM) (sq_nonneg t)
    have hetaSmall : eta ^ 2 < 2 * y * (y + 2) := by
      nlinarith
    have hk2lt : k ^ 2 < 2 := by linarith
    have hsqeta : 0 < eta ^ 2 := sq_pos_of_pos heta
    have hmul : k ^ 2 * eta ^ 2 < 2 * eta ^ 2 :=
      (mul_lt_mul_of_pos_right hk2lt hsqeta)
    have hketa : k * eta < 2 * (y + 1) := by
      have hkepos : 0 < k * eta := mul_pos hk heta
      nlinarith [sq_nonneg (y + 1)]
    have hprod : (1 - M) * (k * eta) <
        (1 - M) * (2 * (y + 1)) :=
      mul_lt_mul_of_pos_left hketa (by linarith)
    unfold contactTCoeff
    nlinarith

/-- A polynomial in the invariants \(a=k\eta\), \(b=\eta^2\), and
\(T=t^2\). -/
private def contactCoreInvariants (a b T y M : ℝ) : ℝ :=
  2 * a * b + (1 - 4 * y) * b - 6 * y ^ 3 - 8 * y ^ 2 +
    (a * (M - 1) + (M + 2) * y + 3 * M + 2) * T

private theorem contactCore_eq_invariants (t y k M eta : ℝ) :
    contactCore t y k M eta =
      contactCoreInvariants (k * eta) (eta ^ 2) (t ^ 2) y M := by
  unfold contactCore contactTCoeff contactCoreInvariants
  ring

/-- The rational parameterization forced by
\(k^2=1+M\) and \(M\eta=kXy\). -/
private def parameterKEta (M X y : ℝ) : ℝ :=
  (1 + M) * X * y / M

private def parameterEtaSq (M X y : ℝ) : ℝ :=
  (1 + M) * X ^ 2 * y ^ 2 / M ^ 2

private def parameterTSq (M X y : ℝ) : ℝ :=
  y * (parameterEtaSq M X y + 2 * y * (y + 2)) / (1 + M * y)

/-- A local transparent spelling of the polynomial, used because its
coefficient definitions in Polynomial.lean are private. -/
private def contactPolynomialExpanded (M X y : ℝ) : ℝ :=
  X ^ 3 * y * (2 - y) +
  X ^ 2 * (X * y ^ 2 + 4 * X * y + 2 * y ^ 2 - 2 * y + 1) * M +
  X * (5 * X ^ 2 * y ^ 2 + 2 * X ^ 2 * y - X * y ^ 2 +
    2 * X * y + X - 2 * y ^ 2 - 4 * y) * M ^ 2 +
  y * (3 * X ^ 3 * y - 3 * X ^ 2 * y + 4 * X ^ 2 + 4 * y + 6) * M ^ 3 +
  2 * (X * y ^ 2 + 2 * X * y - 2 * y ^ 2 + y + 6) * M ^ 4

private theorem contactPolynomial_eq_expanded (M X y : ℝ) :
    contactPolynomial M X y = contactPolynomialExpanded M X y := by
  rfl

/-- Exact algebra behind equation (5.2): after replacing \(t^2\) by its
lower bound, the two-dimensional contact term is the positive polynomial
\(N(M,X,y)\) divided by its positive denominator. -/
private theorem contactCore_parameter_identity {M X y : ℝ}
    (hM : M ≠ 0) (hD : 1 + M * y ≠ 0) :
    contactCoreInvariants (parameterKEta M X y)
        (parameterEtaSq M X y) (parameterTSq M X y) y M =
      y ^ 2 * contactPolynomial M X y / (M ^ 3 * (1 + M * y)) := by
  rw [contactPolynomial_eq_expanded]
  unfold contactCoreInvariants parameterKEta parameterEtaSq parameterTSq
    contactPolynomialExpanded
  dsimp [parameterEtaSq]
  field_simp
  ring

/-- The normalized ratio growth \(X=\chi\) determines both algebraic
invariants used in the contact polynomial. -/
private theorem parameter_relations {M X y k eta : ℝ}
    (hM : M ≠ 0) (hk2 : k ^ 2 = 1 + M)
    (hchi : M * eta = k * X * y) :
    k * eta = parameterKEta M X y ∧
      eta ^ 2 = parameterEtaSq M X y := by
  constructor
  · unfold parameterKEta
    apply (eq_div_iff hM).2
    calc
      (k * eta) * M = k * (M * eta) := by ring
      _ = k * (k * X * y) := by rw [hchi]
      _ = (1 + M) * X * y := by rw [← hk2]; ring
  · unfold parameterEtaSq
    apply (eq_div_iff (pow_ne_zero 2 hM)).2
    calc
      eta ^ 2 * M ^ 2 = (M * eta) ^ 2 := by ring
      _ = (k * X * y) ^ 2 := by rw [hchi]
      _ = (1 + M) * X ^ 2 * y ^ 2 := by rw [← hk2]; ring

/-- Equation (5.2) of the paper: the contact remainder is bounded below
by the explicit polynomial certificate. Positivity of that certificate is
established separately in Polynomial.lean. -/
theorem contactCore_lower_on_contact {r t y k M eta X q : ℝ}
    (hS : contactResidual r t y M eta = 0)
    (hM : 0 < M) (hy : 0 < y)
    (hk : 0 < k) (heta : 0 < eta)
    (hk2 : k ^ 2 = 1 + M)
    (heta2 : eta ^ 2 < r ^ 2 / 2)
    (hchi : M * eta = k * X * y)
    (hq : y ≤ q) (ht : t ^ 2 = r ^ 2 * q) :
    y ^ 2 * contactPolynomial M X y /
        (M ^ 3 * (1 + M * y)) ≤ contactCore t y k M eta := by
  have hD : 0 < 1 + M * y := by positivity
  have hcoef : 0 < contactTCoeff y k M eta :=
    contactTCoeff_pos hS hM hy hk heta hk2 heta2
  obtain ⟨ha, hb⟩ :=
    parameter_relations (ne_of_gt hM) hk2 hchi
  have htl := contact_t_sq_lower hS hq ht
  have htl' :
      y * (parameterEtaSq M X y + 2 * y * (y + 2)) ≤
        (1 + M * y) * t ^ 2 := by
    rw [← hb]
    exact htl
  have hT : parameterTSq M X y ≤ t ^ 2 := by
    unfold parameterTSq
    apply (div_le_iff₀ hD).2
    nlinarith [htl']
  have hcoef' :
      0 < parameterKEta M X y * (M - 1) +
        (M + 2) * y + 3 * M + 2 := by
    rw [← ha]
    exact hcoef
  have hprod :
      0 ≤ (parameterKEta M X y * (M - 1) +
        (M + 2) * y + 3 * M + 2) *
        (t ^ 2 - parameterTSq M X y) :=
    mul_nonneg (le_of_lt hcoef') (sub_nonneg.mpr hT)
  have hcore :
      contactCoreInvariants (parameterKEta M X y)
          (parameterEtaSq M X y) (parameterTSq M X y) y M ≤
        contactCore t y k M eta := by
    rw [contactCore_eq_invariants, ha, hb]
    unfold contactCoreInvariants at *
    nlinarith
  have hidentity :=
    contactCore_parameter_identity (ne_of_gt hM) (ne_of_gt hD)
      (X := X) (y := y)
  rw [hidentity] at hcore
  exact hcore

/-- The full two-dimensional contact remainder is strictly positive on
the profile domain, by the Bernstein certificate for \(N\). -/
theorem contactCore_pos_on_contact {r t y k M eta X q : ℝ}
    (hS : contactResidual r t y M eta = 0)
    (hM : 0 < M) (hy : 0 < y) (hy1 : y < 1)
    (hk : 0 < k) (heta : 0 < eta)
    (hk2 : k ^ 2 = 1 + M)
    (heta2 : eta ^ 2 < r ^ 2 / 2)
    (hX : 0 < X) (hX1 : X < 1)
    (hchi : M * eta = k * X * y)
    (hq : y ≤ q) (ht : t ^ 2 = r ^ 2 * q) :
    0 < contactCore t y k M eta := by
  have hD : 0 < 1 + M * y := by positivity
  have hN : 0 < contactPolynomial M X y :=
    contactPolynomial_pos hM hX hX1 hy hy1
  have hfrac :
      0 < y ^ 2 * contactPolynomial M X y /
          (M ^ 3 * (1 + M * y)) := by positivity
  exact lt_of_lt_of_le hfrac
    (contactCore_lower_on_contact hS hM hy hk heta hk2
      heta2 hchi hq ht)

/-- Combining the polynomial certificate with the positive
\(n-2\) increment yields a strictly positive contact drift. -/
theorem contactDrift_pos_from_bounds {n r t y k M eta X q : ℝ}
    (hn : 2 < n)
    (hS : contactResidual r t y M eta = 0)
    (hM : 0 < M) (hy : 0 < y) (hy1 : y < 1)
    (hk : 0 < k) (heta : 0 < eta)
    (hk2 : k ^ 2 = 1 + M)
    (heta2 : eta ^ 2 < r ^ 2 / 2)
    (hX : 0 < X) (hX1 : X < 1)
    (hchi : M * eta = k * X * y)
    (hq : y ≤ q) (ht : t ^ 2 = r ^ 2 * q) :
    0 < contactDrift n r t y k M eta := by
  exact contactDrift_pos_at_zero hn hy hS
    (le_of_lt <| contactCore_pos_on_contact hS hM hy hy1 hk heta
      hk2 heta2 hX hX1 hchi hq ht)

end

end BrezisOP6
