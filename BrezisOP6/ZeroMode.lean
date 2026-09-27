import BrezisOP6.Picone

/-!
# Removing the zero-mode pole

For `n = m + 3 ≥ 3`, the zero angular mode has coefficient `a = b / r`
and profile contrast `d = r² h`.  The identity below performs the resulting
one-dimensional integration by parts on a finite interval.  It retains both
endpoint fluxes; the passage to the origin is not asserted here.
-/

namespace BrezisOP6

/-- Pointwise zero-mode density identity, with `n = m + 3`.  Its final
derivative is the boundary term that must be kept at finite radius. -/
theorem zeroMode_pointwise
    (m : ℕ) (h b : ℝ → ℝ) (r dh db : ℝ)
    (hr : 0 < r)
    (hh : HasDerivAt h dh r) (hb : HasDerivAt b db r) :
    r ^ (m + 2) * (r ^ 2 * h r) *
        (db / r - b r / r ^ 2) ^ 2
      - (m + 2 : ℝ) * r ^ m * (r ^ 2 * h r) * (b r / r) ^ 2
    = r ^ (m + 2) * h r * db ^ 2
        + r ^ (m + 1) * dh * b r ^ 2
        - deriv (fun x => x ^ (m + 1) * h x * b x ^ 2) r := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hpow : HasDerivAt (fun x : ℝ => x ^ (m + 1))
      ((m + 1 : ℝ) * r ^ m) r := by
    simpa using (hasDerivAt_pow (m + 1) r)
  have hflux : HasDerivAt (fun x => x ^ (m + 1) * h x * b x ^ 2)
      (((m + 1 : ℝ) * r ^ m * h r + r ^ (m + 1) * dh) * b r ^ 2
        + (r ^ (m + 1) * h r) * (2 * b r * db)) r := by
    convert ((hpow.mul hh).mul (hb.pow 2)) using 1
    simp only [Pi.pow_apply, Pi.mul_apply]
    ring
  rw [hflux.deriv]
  field_simp [hr_ne]
  ring

/-- The exact zero-mode integration by parts on `[a,R]`, with `0<a≤R`.
The left side is the degree-zero angular contribution after setting
`a₀=b/r` and `d=r²h`; the last line displays **both** endpoint terms.
No assertion about the limit `a↓0` is built into this result. -/
theorem zeroMode_interval
    (m : ℕ) (h b dh db : ℝ → ℝ) (a R : ℝ)
    (ha : 0 < a) (haR : a ≤ R)
    (hh_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt h (dh x) x)
    (hb_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt b (db x) x)
    (hgrad_int : IntervalIntegrable
      (fun x => x ^ (m + 2) * h x * db x ^ 2)
      MeasureTheory.volume a R)
    (hpot_int : IntervalIntegrable
      (fun x => x ^ (m + 1) * dh x * b x ^ 2)
      MeasureTheory.volume a R)
    (hflux_int : IntervalIntegrable
      (deriv fun x => x ^ (m + 1) * h x * b x ^ 2)
      MeasureTheory.volume a R) :
    (∫ x in a..R,
      x ^ (m + 2) * (x ^ 2 * h x) *
        (deriv (fun s => b s / s) x) ^ 2
      - (m + 2 : ℝ) * x ^ m * (x ^ 2 * h x) * (b x / x) ^ 2) =
      (∫ x in a..R, x ^ (m + 2) * h x * db x ^ 2)
      + (∫ x in a..R, x ^ (m + 1) * dh x * b x ^ 2)
      - (R ^ (m + 1) * h R * b R ^ 2
         - a ^ (m + 1) * h a * b a ^ 2) := by
  let flux : ℝ → ℝ := fun x => x ^ (m + 1) * h x * b x ^ 2
  let grad : ℝ → ℝ := fun x => x ^ (m + 2) * h x * db x ^ 2
  let pot : ℝ → ℝ := fun x => x ^ (m + 1) * dh x * b x ^ 2
  have hflux_diff : ∀ x ∈ Set.uIcc a R, DifferentiableAt ℝ flux x := by
    intro x hx
    exact (((hasDerivAt_pow (m + 1) x).mul (hh_deriv x hx)).mul
      ((hb_deriv x hx).pow 2)).differentiableAt
  have hpoint : Set.EqOn
      (fun x => x ^ (m + 2) * (x ^ 2 * h x) *
          (deriv (fun s => b s / s) x) ^ 2
        - (m + 2 : ℝ) * x ^ m * (x ^ 2 * h x) * (b x / x) ^ 2)
      (fun x => grad x + pot x - deriv flux x)
      (Set.uIcc a R) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a R := by
      simpa [Set.uIcc_of_le haR] using hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hxIcc.1
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hquot : deriv (fun s => b s / s) x =
        db x / x - b x / x ^ 2 := by
      have hderiv := (hb_deriv x hx).div (hasDerivAt_id x) hxne
      convert hderiv.deriv using 1
      simp only [id_eq]
      field_simp [hxne]
    simpa only [hquot] using
      (zeroMode_pointwise m h b x (dh x) (db x) hxpos
        (hh_deriv x hx) (hb_deriv x hx))
  calc
    (∫ x in a..R,
      x ^ (m + 2) * (x ^ 2 * h x) *
        (deriv (fun s => b s / s) x) ^ 2
      - (m + 2 : ℝ) * x ^ m * (x ^ 2 * h x) * (b x / x) ^ 2) =
        ∫ x in a..R, grad x + pot x - deriv flux x :=
      intervalIntegral.integral_congr hpoint
    _ = (∫ x in a..R, grad x) + (∫ x in a..R, pot x)
        - (flux R - flux a) := by
      rw [intervalIntegral.integral_sub (hgrad_int.add hpot_int) hflux_int,
        intervalIntegral.integral_add hgrad_int hpot_int,
        intervalIntegral.integral_deriv_eq_sub hflux_diff hflux_int]
    _ = _ := rfl

end BrezisOP6
