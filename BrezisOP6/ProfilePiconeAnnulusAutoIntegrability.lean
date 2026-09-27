import BrezisOP6.PiconeAnnulusIntegrability

/-!
# Annular Picone integrability from the density and flux

On a positive annulus the pointwise Picone identity splits an integrable
quantity into two nonnegative pieces. Measurability of those pieces is
enough to derive their individual integrability.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem profilePicone_annulus_parts_intervalIntegrable
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hFpos : ∀ x ∈ uIcc δ R, 0 < F x)
    (hMpos : ∀ x ∈ uIcc δ R, 0 < profileM f F x)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ x ∈ uIoo δ R,
      HasDerivAt (deriv f) (f₂ x) x)
    (hdF : ∀ x ∈ uIoo δ R,
      HasDerivAt (deriv F) (F₂ x) x)
    (hode_f : ∀ x ∈ uIoo δ R,
      radialODEAt ((m : ℝ) + 3) x (f x) (deriv f x) (f₂ x))
    (hode_F : ∀ x ∈ uIoo δ R,
      radialODEAt ((m : ℝ) + 3) x (F x) (deriv F x) (F₂ x))
    (hb : ∀ x ∈ uIoo δ R, HasDerivAt b (db x) x)
    (hS : ∀ x ∈ uIcc δ R,
      0 ≤ contactResidual x (profileT F x) (profileY F x)
        (profileK f F x ^ 2 - 1) (profileEta f F x))
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      volume δ R)
    (hfluxInt : IntervalIntegrable
      (deriv (profilePiconeBoundaryFlux m f F b)) volume δ R)
    (hremMeas : AEStronglyMeasurable
      (profilePiconeRemainder m f F b)
      (volume.restrict (Ioc δ R))) :
    IntervalIntegrable (profilePiconeSquare m f F b db)
      volume δ R ∧
    IntervalIntegrable (profilePiconeRemainder m f F b)
      volume δ R := by
  have hEq : (profilePiconeDensity m f F b db) =ᵐ[
      volume.restrict (Ioc δ R)]
      fun x => profilePiconeSquare m f F b db x +
        deriv (profilePiconeBoundaryFlux m f F b) x +
        profilePiconeRemainder m f F b x := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    have hxpos : 0 < x := lt_trans hδ hx.1
    have hxClosed : x ∈ uIcc δ R :=
      uIoo_subset_uIcc_self (by simpa [uIoo_of_le hδR] using hx)
    have hxOpen : x ∈ uIoo δ R := by
      simpa [uIoo_of_le hδR] using hx
    have hraw := radial_picone_pointwise_from_profiles m f F b x
      (deriv f x) (deriv F x) (f₂ x) (F₂ x) (db x)
      hxpos (hFpos x hxClosed) (hMpos x hxClosed) hfDiff hFDiff
      (hfDiff x).hasDerivAt (hFDiff x).hasDerivAt
      (hdf x hxOpen) (hdF x hxOpen)
      (hode_f x hxOpen) (hode_F x hxOpen) (hb x hxOpen)
    simpa only [profilePiconeDensity, profilePiconeSquare,
      profilePiconeBoundaryFlux, profilePiconeRemainder] using hraw
  have hSqNonneg : ∀ᵐ x ∂volume.restrict (Ioc δ R),
      0 ≤ profilePiconeSquare m f F b db x := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro x hx
    have hxClosed : x ∈ uIcc δ R := by
      simpa [uIcc_of_le hδR] using ⟨hx.1.le, hx.2⟩
    have hxpos : 0 < x := lt_trans hδ hx.1
    have hhpos := piconeWeight_pos f F x hxpos
      (hFpos x hxClosed) (hMpos x hxClosed)
    have hphipos := piconeMultiplier_pos f F x hxpos
      (hFpos x hxClosed) (hMpos x hxClosed)
    unfold profilePiconeSquare
    positivity
  have hRemNonneg : ∀ᵐ x ∂volume.restrict (Ioc δ R),
      0 ≤ profilePiconeRemainder m f F b x := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro x hx
    have hxClosed : x ∈ uIcc δ R := by
      simpa [uIcc_of_le hδR] using ⟨hx.1.le, hx.2⟩
    have hxpos : 0 < x := lt_trans hδ hx.1
    have hhpos := piconeWeight_pos f F x hxpos
      (hFpos x hxClosed) (hMpos x hxClosed)
    have hSpos := hS x hxClosed
    unfold profilePiconeRemainder
    positivity
  have hSqMeas : AEStronglyMeasurable
      (profilePiconeSquare m f F b db)
      (volume.restrict (Ioc δ R)) := by
    have hSqEq : (fun x =>
        profilePiconeDensity m f F b db x -
          deriv (profilePiconeBoundaryFlux m f F b) x -
          profilePiconeRemainder m f F b x) =ᵐ[
        volume.restrict (Ioc δ R)]
        profilePiconeSquare m f F b db := by
      filter_upwards [hEq] with x hx
      rw [hx]
      ring
    exact ((hDint.aestronglyMeasurable.sub
      hfluxInt.aestronglyMeasurable).sub hremMeas).congr hSqEq
  exact annulus_nonnegative_parts_integrable_of_density_flux
    (profilePiconeDensity m f F b db)
    (deriv (profilePiconeBoundaryFlux m f F b))
    (profilePiconeSquare m f F b db)
    (profilePiconeRemainder m f F b) δ R hδR
    hDint hfluxInt hEq hSqMeas hremMeas hSqNonneg hRemNonneg

end

end BrezisOP6
