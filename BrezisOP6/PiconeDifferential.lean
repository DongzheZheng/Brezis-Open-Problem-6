import BrezisOP6.PiconeResidual

/-!
# Weighted differential form of the zero-mode Picone residual

The algebraic flow certificate is connected here to an actual derivative of
the weighted multiplier flux.  Working with the logarithmic slope
`P = r φ'/φ` avoids a second derivative of `φ`.
-/

namespace BrezisOP6

noncomputable section

/-- The local differential identity behind the Picone calculation.  The
dimension is `n=m+3`, so this covers exactly `n≥3`.  No division by a
possibly vanishing profile occurs in this statement. -/
theorem picone_weighted_flux_identity
    (m : ℕ) (h phi P : ℝ → ℝ) (r dh dphi dP piH : ℝ)
    (hh : HasDerivAt h dh r)
    (hphi : HasDerivAt phi dphi r)
    (hP : HasDerivAt P dP r)
    (hweight : r * dh = h r * piH)
    (hmult : r * dphi = phi r * P r) :
    r ^ (m + 1) * dh * phi r -
        deriv (fun x => x ^ (m + 1) * h x * phi x * P x) r =
      r ^ m * h r * phi r *
        piconeLogResidual (m + 3) piH (P r) (r * dP) := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (m + 1))
      ((m + 1 : ℝ) * r ^ m) r := by
    simpa using (hasDerivAt_pow (m + 1) r)
  have hflux : HasDerivAt
      (fun x => x ^ (m + 1) * h x * phi x * P x)
      ((((m + 1 : ℝ) * r ^ m * h r + r ^ (m + 1) * dh) * phi r
        + r ^ (m + 1) * h r * dphi) * P r
        + r ^ (m + 1) * h r * phi r * dP) r := by
    convert (((hpow.mul hh).mul hphi).mul hP) using 1
  rw [hflux.deriv]
  rw [pow_succ]
  unfold piconeLogResidual
  calc
    r ^ m * r * dh * phi r -
        ((((m + 1 : ℝ) * r ^ m * h r + r ^ m * r * dh) * phi r
          + r ^ m * r * h r * dphi) * P r
          + r ^ m * r * h r * phi r * dP) =
      r ^ m * h r * phi r *
        (piH - r * dP - ((m + 3 : ℕ) : ℝ) * P r +
          2 * P r - piH * P r - (P r) ^ 2) +
        r ^ m * phi r * (1 - P r) * (r * dh - h r * piH) -
        r ^ m * h r * P r * (r * dphi - phi r * P r) := by
      push_cast
      ring
    _ = r ^ m * h r * phi r *
        (piH - r * dP - ((m + 3 : ℕ) : ℝ) * P r +
          2 * P r - piH * P r - (P r) ^ 2) := by
      rw [hweight, hmult]
      ring
    _ = _ := by
      push_cast
      ring

/-- The weighted zero-mode differential identity with the profile flow
substituted.  The slope equations for `h` and `φ` are explicit assumptions;
their verification from the two original profiles is a separate task. -/
theorem picone_weighted_flux_eq_contactResidual
    (m : ℕ) (h phi y k eta : ℝ → ℝ)
    (r t dh dphi dy dk deta : ℝ)
    (hh : HasDerivAt h dh r)
    (hphi : HasDerivAt phi dphi r)
    (hy : HasDerivAt y dy r)
    (hk : HasDerivAt k dk r)
    (heta : HasDerivAt eta deta r)
    (hweight : r * dh = h r * piconeWeightLogSlope (y r) (k r) (eta r))
    (hmult : r * dphi = phi r * piconeMultiplierLogSlope (y r) (k r) (eta r))
    (hyFlow : r * dy = y r ^ 2 - ((m : ℝ) + 3) * y r + r ^ 2 - t ^ 2)
    (hkFlow : r * dk = (k r ^ 2 - 1) * eta r)
    (hetaFlow : r * deta = k r * t ^ 2 -
      (((m : ℝ) + 3) - 2 * y r) * eta r - 2 * k r * eta r ^ 2) :
    r ^ (m + 1) * dh * phi r -
        deriv (fun x => x ^ (m + 1) * h x * phi x *
          piconeMultiplierLogSlope (y x) (k x) (eta x)) r =
      r ^ m * h r * phi r *
        contactResidual r t (y r) (k r ^ 2 - 1) (eta r) := by
  let P : ℝ → ℝ := fun x =>
    piconeMultiplierLogSlope (y x) (k x) (eta x)
  have hP : HasDerivAt P
      (-(dy + dk * eta r + k r * deta)) r := by
    convert (hy.add (hk.mul heta)).neg using 1
    dsimp [P, piconeMultiplierLogSlope]
    ring
  have hRate : r * (-(dy + dk * eta r + k r * deta)) =
      piconeMultiplierLogRate
        (y r ^ 2 - ((m : ℝ) + 3) * y r + r ^ 2 - t ^ 2)
        ((k r ^ 2 - 1) * eta r)
        (k r * t ^ 2 - (((m : ℝ) + 3) - 2 * y r) * eta r -
          2 * k r * eta r ^ 2) (k r) (eta r) := by
    unfold piconeMultiplierLogRate
    calc
      r * (-(dy + dk * eta r + k r * deta)) =
          -(r * dy + (r * dk) * eta r + k r * (r * deta)) := by ring
      _ = _ := by rw [hyFlow, hkFlow, hetaFlow]
  have hbase := picone_weighted_flux_identity m h phi P r dh dphi
    (-(dy + dk * eta r + k r * deta))
    (piconeWeightLogSlope (y r) (k r) (eta r))
    hh hphi hP hweight hmult
  change _ = _ at hbase
  simpa only [P, hRate, Nat.cast_add, Nat.cast_ofNat,
    piconeLogResidual_eq_contactResidual] using hbase

end

end BrezisOP6
