import BrezisOP6.ProfilePiconeInterval
import BrezisOP6.EnergyIBPInterior

/-!
# Profile Picone identity with one-sided outer endpoint

The radial equations, second derivatives and test-mode derivative occur only
on an open annulus.  The Picone flux is continuous on its closure, and its
fundamental theorem therefore uses no derivative at the finite-ball edge.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem profilePicone_interval_interior
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hFpos : ∀ x ∈ Set.uIcc δ R, 0 < F x)
    (hMpos : ∀ x ∈ Set.uIcc δ R, 0 < profileM f F x)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ x ∈ Set.uIoo δ R,
      HasDerivAt (deriv f) (f₂ x) x)
    (hdF : ∀ x ∈ Set.uIoo δ R,
      HasDerivAt (deriv F) (F₂ x) x)
    (hode_f : ∀ x ∈ Set.uIoo δ R,
      radialODEAt ((m : ℝ) + 3) x (f x) (deriv f x) (f₂ x))
    (hode_F : ∀ x ∈ Set.uIoo δ R,
      radialODEAt ((m : ℝ) + 3) x (F x) (deriv F x) (F₂ x))
    (hb : ∀ x ∈ Set.uIoo δ R, HasDerivAt b (db x) x)
    (hsq_int : IntervalIntegrable (profilePiconeSquare m f F b db)
      MeasureTheory.volume δ R)
    (hflux_cont : ContinuousOn (profilePiconeBoundaryFlux m f F b)
      (Set.uIcc δ R))
    (hflux_int : IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b))
      MeasureTheory.volume δ R)
    (hrem_int : IntervalIntegrable (profilePiconeRemainder m f F b)
      MeasureTheory.volume δ R) :
    (∫ x in δ..R, profilePiconeDensity m f F b db x) =
      (∫ x in δ..R, profilePiconeSquare m f F b db x) +
      (profilePiconeBoundaryFlux m f F b R -
        profilePiconeBoundaryFlux m f F b δ) +
      (∫ x in δ..R, profilePiconeRemainder m f F b x) := by
  have hflux_diff : ∀ x ∈ Set.uIoo δ R,
      DifferentiableAt ℝ (profilePiconeBoundaryFlux m f F b) x := by
    intro x hx
    have hxIcc : x ∈ Set.Ioo δ R := by
      simpa [Set.uIoo_of_le hδR] using hx
    have hxpos : 0 < x := lt_trans hδ hxIcc.1
    have hxClosed : x ∈ Set.uIcc δ R :=
      Set.uIoo_subset_uIcc_self hx
    exact profilePiconeBoundaryFlux_differentiableAt m f F b x
      (deriv f x) (deriv F x) (f₂ x) (F₂ x) (db x)
      hxpos (hFpos x hxClosed) (hMpos x hxClosed) hfDiff hFDiff
      (hfDiff x).hasDerivAt (hFDiff x).hasDerivAt
      (hdf x hx) (hdF x hx) (hb x hx)
  have hpoint : Set.EqOn
      (profilePiconeDensity m f F b db)
      (fun x => profilePiconeSquare m f F b db x +
        deriv (profilePiconeBoundaryFlux m f F b) x +
        profilePiconeRemainder m f F b x)
      (Set.uIoo δ R) := by
    intro x hx
    have hxIcc : x ∈ Set.Ioo δ R := by
      simpa [Set.uIoo_of_le hδR] using hx
    have hxpos : 0 < x := lt_trans hδ hxIcc.1
    have hxClosed : x ∈ Set.uIcc δ R :=
      Set.uIoo_subset_uIcc_self hx
    have hraw := radial_picone_pointwise_from_profiles m f F b x
      (deriv f x) (deriv F x) (f₂ x) (F₂ x) (db x)
      hxpos (hFpos x hxClosed) (hMpos x hxClosed) hfDiff hFDiff
      (hfDiff x).hasDerivAt (hFDiff x).hasDerivAt
      (hdf x hx) (hdF x hx) (hode_f x hx) (hode_F x hx)
      (hb x hx)
    simpa only [profilePiconeDensity, profilePiconeSquare,
      profilePiconeBoundaryFlux, profilePiconeRemainder] using hraw
  calc
    (∫ x in δ..R, profilePiconeDensity m f F b db x) =
      ∫ x in δ..R, profilePiconeSquare m f F b db x +
        deriv (profilePiconeBoundaryFlux m f F b) x +
        profilePiconeRemainder m f F b x :=
      interval_integral_congr_interior hpoint
    _ = _ := by
      rw [intervalIntegral.integral_add (hsq_int.add hflux_int) hrem_int,
        intervalIntegral.integral_add hsq_int hflux_int,
        intervalIntegral.integral_deriv_eq_sub_uIoo hflux_cont hflux_diff hflux_int]



/-- If `S≥0` on `[δ,R]` and `b(R)=0`, the zero-mode density dominates
the negative inner boundary flux.  The inner flux remains explicit. -/
theorem profilePicone_interval_lower_bound_interior
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hFpos : ∀ x ∈ Set.uIcc δ R, 0 < F x)
    (hMpos : ∀ x ∈ Set.uIcc δ R, 0 < profileM f F x)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ x ∈ Set.uIoo δ R,
      HasDerivAt (deriv f) (f₂ x) x)
    (hdF : ∀ x ∈ Set.uIoo δ R,
      HasDerivAt (deriv F) (F₂ x) x)
    (hode_f : ∀ x ∈ Set.uIoo δ R,
      radialODEAt ((m : ℝ) + 3) x (f x) (deriv f x) (f₂ x))
    (hode_F : ∀ x ∈ Set.uIoo δ R,
      radialODEAt ((m : ℝ) + 3) x (F x) (deriv F x) (F₂ x))
    (hb : ∀ x ∈ Set.uIoo δ R, HasDerivAt b (db x) x)
    (hS : ∀ x ∈ Set.uIcc δ R,
      0 ≤ contactResidual x (profileT F x) (profileY F x)
        (profileK f F x ^ 2 - 1) (profileEta f F x))
    (hbR : b R = 0)
    (hsq_int : IntervalIntegrable (profilePiconeSquare m f F b db)
      MeasureTheory.volume δ R)
    (hflux_cont : ContinuousOn (profilePiconeBoundaryFlux m f F b)
      (Set.uIcc δ R))
    (hflux_int : IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b))
      MeasureTheory.volume δ R)
    (hrem_int : IntervalIntegrable (profilePiconeRemainder m f F b)
      MeasureTheory.volume δ R) :
    -profilePiconeBoundaryFlux m f F b δ ≤
      ∫ x in δ..R, profilePiconeDensity m f F b db x := by
  have hsq_nonneg : 0 ≤
      ∫ x in δ..R, profilePiconeSquare m f F b db x := by
    apply intervalIntegral.integral_nonneg hδR
    intro x hx
    have hxU : x ∈ Set.uIcc δ R := by
      simpa [Set.uIcc_of_le hδR] using hx
    have hxpos : 0 < x := lt_of_lt_of_le hδ hx.1
    have hhpos := piconeWeight_pos f F x hxpos (hFpos x hxU)
      (hMpos x hxU)
    unfold profilePiconeSquare
    have hphipos := piconeMultiplier_pos f F x hxpos
      (hFpos x hxU) (hMpos x hxU)
    positivity
  have hrem_nonneg : 0 ≤
      ∫ x in δ..R, profilePiconeRemainder m f F b x := by
    apply intervalIntegral.integral_nonneg hδR
    intro x hx
    have hxU : x ∈ Set.uIcc δ R := by
      simpa [Set.uIcc_of_le hδR] using hx
    have hxpos : 0 < x := lt_of_lt_of_le hδ hx.1
    have hhpos := piconeWeight_pos f F x hxpos (hFpos x hxU)
      (hMpos x hxU)
    have hSpos := hS x hxU
    unfold profilePiconeRemainder
    positivity
  have houter : profilePiconeBoundaryFlux m f F b R = 0 := by
    simp [profilePiconeBoundaryFlux, hbR]
  have hident := profilePicone_interval_interior m f F b db f₂ F₂ δ R
    hδ hδR hFpos hMpos hfDiff hFDiff hdf hdF hode_f hode_F hb
    hsq_int hflux_cont hflux_int hrem_int
  rw [houter] at hident
  linarith

end

end BrezisOP6
