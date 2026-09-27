import BrezisOP6.EnergyQuotientGradientBound

/-!
# Termwise majorant for the spherical quadratic bridge

The two-profile coefficient `d=f²−F²` lies between zero and `f²` when
`0≤F≤f`.  Consequently each radial or angular derivative term inherits
the already proved estimate for `f²|∇z|²`, and each zeroth-order term
inherits `f²|z|²=|u|²`.  The apparent singularity is then governed by
the integrable powers `r^m` and `r^(m+2)` in dimension `m+3`.
-/

namespace BrezisOP6

noncomputable section

/-- Algebraic core of the termwise spherical estimate.  `G` can denote
the squared full gradient, or a bounded radial/tangential component;
`Z` denotes a squared field component. -/
theorem radial_bridge_termwise_abs_bound
    (m : ℕ) (r f d G Z A B C : ℝ)
    (hr : 0 < r) (hd0 : 0 ≤ d) (hdle : d ≤ f ^ 2)
    (hG0 : 0 ≤ G) (hZ0 : 0 ≤ Z)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hG : f ^ 2 * G ≤ A + B * r⁻¹ ^ 2)
    (hZ : f ^ 2 * Z ≤ C) :
    |r ^ (m + 2) * d * G -
        ((m : ℝ) + 2) * r ^ m * d * Z| ≤
      r ^ m * (A * r ^ 2 + B + ((m : ℝ) + 2) * C) := by
  have hrm : 0 ≤ r ^ m := pow_nonneg hr.le _
  have hrm2 : 0 ≤ r ^ (m + 2) := pow_nonneg hr.le _
  have hcoef : 0 ≤ (m : ℝ) + 2 := by positivity
  have hgradTerm : r ^ (m + 2) * d * G ≤
      r ^ m * (A * r ^ 2 + B) := by
    have hDG : d * G ≤ f ^ 2 * G :=
      mul_le_mul_of_nonneg_right hdle hG0
    have hweighted : d * G ≤ A + B * r⁻¹ ^ 2 :=
      hDG.trans hG
    have hmul := mul_le_mul_of_nonneg_left hweighted hrm2
    have hid : r ^ (m + 2) * (A + B * r⁻¹ ^ 2) =
        r ^ m * (A * r ^ 2 + B) := by
      rw [pow_add]
      field_simp [ne_of_gt hr]
    nlinarith [hmul]
  have hzeroTerm : r ^ m * d * Z ≤ r ^ m * C := by
    have hDZ : d * Z ≤ f ^ 2 * Z :=
      mul_le_mul_of_nonneg_right hdle hZ0
    have h := mul_le_mul_of_nonneg_left (hDZ.trans hZ) hrm
    nlinarith
  have hfirst : 0 ≤ r ^ (m + 2) * d * G := by positivity
  have hsecond : 0 ≤ ((m : ℝ) + 2) * r ^ m * d * Z := by positivity
  have habs : |r ^ (m + 2) * d * G -
      ((m : ℝ) + 2) * r ^ m * d * Z| ≤
      r ^ (m + 2) * d * G +
        ((m : ℝ) + 2) * r ^ m * d * Z := by
    calc
      _ = |r ^ (m + 2) * d * G +
          -(((m : ℝ) + 2) * r ^ m * d * Z)| := by ring
      _ ≤ |r ^ (m + 2) * d * G| +
          |-(((m : ℝ) + 2) * r ^ m * d * Z)| :=
        abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg hfirst, abs_neg,
        abs_of_nonneg hsecond]
  have hzeroScaled := mul_le_mul_of_nonneg_left hzeroTerm hcoef
  nlinarith [habs, hgradTerm, hzeroScaled]

end

end BrezisOP6
