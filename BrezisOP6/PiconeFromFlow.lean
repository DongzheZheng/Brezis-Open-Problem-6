import BrezisOP6.PiconeDifferential
import BrezisOP6.Picone

/-!
# Pointwise zero-mode ground-state identity from the profile flow

The profile-flow calculation gives an exact Picone residual.  This module
combines it with the general Picone identity, including the derivative of the
boundary flux.  All statements are pointwise for `r>0`; the radial interval
and endpoint passage are separate.
-/

namespace BrezisOP6

noncomputable section

def radialPiconeWeight (m : ℕ) (h : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 2) * h r

def radialPiconeTheta (m : ℕ) (h phi y k eta : ℝ → ℝ)
    (r : ℝ) : ℝ :=
  r ^ (m + 1) * h r * phi r *
    piconeMultiplierLogSlope (y r) (k r) (eta r)

/-- The exact residual potential in the zero-mode Picone transform. -/
theorem radial_picone_residual_from_flow
    (m : ℕ) (h phi y k eta : ℝ → ℝ)
    (r t dh dphi dy dk deta : ℝ)
    (hphiPos : 0 < phi r)
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
    r ^ (m + 1) * dh -
        deriv (radialPiconeTheta m h phi y k eta) r / phi r =
      r ^ m * h r *
        contactResidual r t (y r) (k r ^ 2 - 1) (eta r) := by
  have hbase := picone_weighted_flux_eq_contactResidual
    m h phi y k eta r t dh dphi dy dk deta hh hphi hy hk heta
    hweight hmult hyFlow hkFlow hetaFlow
  change r ^ (m + 1) * dh * phi r -
      deriv (radialPiconeTheta m h phi y k eta) r =
      r ^ m * h r * phi r *
        contactResidual r t (y r) (k r ^ 2 - 1) (eta r) at hbase
  field_simp [ne_of_gt hphiPos]
  nlinarith [hbase]

/-- At one positive radius, the zero-mode quadratic density is a positive
Picone square plus a total derivative and the explicit `S` remainder. -/
theorem radial_picone_pointwise_from_flow
    (m : ℕ) (h phi y k eta b : ℝ → ℝ)
    (r t dh dphi dy dk deta db : ℝ)
    (hphiPos : 0 < phi r)
    (hh : HasDerivAt h dh r)
    (hphi : HasDerivAt phi dphi r)
    (hy : HasDerivAt y dy r)
    (hk : HasDerivAt k dk r)
    (heta : HasDerivAt eta deta r)
    (hb : HasDerivAt b db r)
    (hweight : r * dh = h r * piconeWeightLogSlope (y r) (k r) (eta r))
    (hmult : r * dphi = phi r * piconeMultiplierLogSlope (y r) (k r) (eta r))
    (hyFlow : r * dy = y r ^ 2 - ((m : ℝ) + 3) * y r + r ^ 2 - t ^ 2)
    (hkFlow : r * dk = (k r ^ 2 - 1) * eta r)
    (hetaFlow : r * deta = k r * t ^ 2 -
      (((m : ℝ) + 3) - 2 * y r) * eta r - 2 * k r * eta r ^ 2) :
    r ^ (m + 2) * h r * db ^ 2 +
        r ^ (m + 1) * dh * b r ^ 2 =
      r ^ (m + 2) * h r * phi r ^ 2 *
        (db / phi r - b r * dphi / phi r ^ 2) ^ 2 +
      deriv (fun x => radialPiconeTheta m h phi y k eta x /
        phi x * b x ^ 2) r +
      r ^ m * h r *
        contactResidual r t (y r) (k r ^ 2 - 1) (eta r) * b r ^ 2 := by
  let P : ℝ → ℝ := fun x =>
    piconeMultiplierLogSlope (y x) (k x) (eta x)
  have hP : HasDerivAt P (-(dy + dk * eta r + k r * deta)) r := by
    convert (hy.add (hk.mul heta)).neg using 1
    dsimp [P, piconeMultiplierLogSlope]
    ring
  have hpow : HasDerivAt (fun x : ℝ => x ^ (m + 1))
      ((m + 1 : ℝ) * r ^ m) r := by
    simpa using (hasDerivAt_pow (m + 1) r)
  have htheta : HasDerivAt (radialPiconeTheta m h phi y k eta)
      ((((m + 1 : ℝ) * r ^ m * h r + r ^ (m + 1) * dh) * phi r
        + r ^ (m + 1) * h r * dphi) * P r
        + r ^ (m + 1) * h r * phi r *
          (-(dy + dk * eta r + k r * deta))) r := by
    convert (((hpow.mul hh).mul hphi).mul hP) using 1
  have hthetaAt : radialPiconeTheta m h phi y k eta r =
      radialPiconeWeight m h r * dphi := by
    unfold radialPiconeTheta radialPiconeWeight
    rw [pow_succ]
    calc
      r ^ m * r * h r * phi r *
          piconeMultiplierLogSlope (y r) (k r) (eta r) =
        r ^ m * h r * (phi r *
          piconeMultiplierLogSlope (y r) (k r) (eta r)) * r := by ring
      _ = r ^ m * h r * (r * dphi) * r := by rw [hmult]
      _ = r ^ (m + 2) * h r * dphi := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ, pow_succ]
        ring
  have hpic := picone_pointwise
    (radialPiconeWeight m h)
    (fun x => x ^ (m + 1) * deriv h x)
    phi (radialPiconeTheta m h phi y k eta) b
    r dphi
    ((((m + 1 : ℝ) * r ^ m * h r + r ^ (m + 1) * dh) * phi r
        + r ^ (m + 1) * h r * dphi) * P r
        + r ^ (m + 1) * h r * phi r *
          (-(dy + dk * eta r + k r * deta)))
    db hphiPos hphi htheta hb hthetaAt
  have hres := radial_picone_residual_from_flow m h phi y k eta
    r t dh dphi dy dk deta hphiPos hh hphi hy hk heta
    hweight hmult hyFlow hkFlow hetaFlow
  unfold radialPiconeWeight at hpic
  dsimp only at hpic
  rw [hh.deriv] at hpic
  rw [← htheta.deriv] at hpic
  -- The general Picone identity now has precisely the profile residual.
  calc
    r ^ (m + 2) * h r * db ^ 2 +
        r ^ (m + 1) * dh * b r ^ 2 =
      r ^ (m + 2) * h r * phi r ^ 2 *
        (db / phi r - b r * dphi / phi r ^ 2) ^ 2 +
      deriv (fun x => radialPiconeTheta m h phi y k eta x /
        phi x * b x ^ 2) r +
      (r ^ (m + 1) * dh -
        deriv (radialPiconeTheta m h phi y k eta) r / phi r) * b r ^ 2 := by
      simpa using hpic
    _ = _ := by rw [hres]

end

end BrezisOP6
