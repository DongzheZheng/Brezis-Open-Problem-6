import BrezisOP6.ProfilePiconeAnnulusAutoIntegrability

/-!
# Measurability of the profile Picone remainder

Only first derivatives of the two profiles occur in the contact residual.
Consequently the remainder is continuous on the punctured radial interval
when the profiles are C¹ and the mode itself is continuous there.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem profilePiconeRemainder_aestronglyMeasurable_of_b_continuousOn
    (m : ℕ) (f F b : ℝ → ℝ) (δ R : ℝ)
    (hfMeas : Measurable f) (hFMeas : Measurable F)
    (hbCont : ContinuousOn b (Ioo δ R)) :
    AEStronglyMeasurable (profilePiconeRemainder m f F b)
      (volume.restrict (Ioc δ R)) := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  let μ := volume.restrict (Ioo δ R)
  have hb : AEStronglyMeasurable b μ :=
    hbCont.aestronglyMeasurable measurableSet_Ioo
  have hK : Measurable (profileK f F) := by
    simpa only [profileK] using hfMeas.div hFMeas
  have hM : Measurable (profileM f F) := by
    simpa only [profileM, ratioM] using
      (hK.pow_const 2).sub measurable_const
  have hEta : Measurable (profileEta f F) := by
    simpa only [profileEta] using
      (measurable_id.mul (measurable_deriv (profileK f F))).div hM
  have hY : Measurable (profileY F) := by
    simpa only [profileY] using
      measurable_const.sub
        ((measurable_id.mul (measurable_deriv F)).div hFMeas)
  have hT : Measurable (profileT F) := by
    simpa only [profileT] using measurable_id.mul hFMeas
  have hW : Measurable (piconeWeightFromProfiles f F) := by
    simpa only [piconeWeightFromProfiles] using
      ((hfMeas.pow_const 2).sub (hFMeas.pow_const 2)).div
        (measurable_id.pow_const 2)
  have hContact : Measurable
      (fun r => contactResidual r (profileT F r) (profileY F r)
        (profileK f F r ^ 2 - 1) (profileEta f F r)) := by
    dsimp only [contactResidual]
    exact (((((measurable_id.pow_const 2).add
      (((hK.pow_const 2).sub measurable_const).mul (hT.pow_const 2))).sub
      (measurable_const.mul hY)).sub
      (measurable_const.mul (hY.pow_const 2))).sub
      (hEta.pow_const 2))
  have hcoeff : Measurable (fun r : ℝ =>
      r ^ m * piconeWeightFromProfiles f F r *
        contactResidual r (profileT F r) (profileY F r)
          (profileK f F r ^ 2 - 1) (profileEta f F r)) :=
    ((measurable_id.pow_const m).mul hW).mul hContact
  simpa only [profilePiconeRemainder] using
    hcoeff.aestronglyMeasurable.mul (hb.pow 2)

theorem profilePiconeRemainder_continuousOn_punctured
    (m : ℕ) (f F b : ℝ → ℝ) (R : ℝ)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (hFpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < F r)
    (hMpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < profileM f F r)
    (hbCont : ContinuousOn b (Ioo (0 : ℝ) R)) :
    ContinuousOn (profilePiconeRemainder m f F b)
      (Ioo (0 : ℝ) R) := by
  let V : Set ℝ := Ioo (0 : ℝ) R
  have hfCont : ContinuousOn f V := hfC1.continuous.continuousOn
  have hFCont : ContinuousOn F V := hFC1.continuous.continuousOn
  have hKdiff : ContDiffOn ℝ 1 (profileK f F) V := by
    simpa only [profileK] using
      (hfC1.contDiffOn.div hFC1.contDiffOn
        (fun r hr => ne_of_gt (hFpos r hr)))
  have hKCont : ContinuousOn (profileK f F) V :=
    hKdiff.continuousOn
  have hKderCont : ContinuousOn (deriv (profileK f F)) V :=
    hKdiff.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)
  have hFderCont : ContinuousOn (deriv F) V :=
    hFC1.contDiffOn.continuousOn_deriv_of_isOpen
      isOpen_Ioo (le_refl 1)
  have hMCont : ContinuousOn (profileM f F) V := by
    simpa only [profileM, ratioM] using
      (hKCont.pow 2).sub continuousOn_const
  have hEtaCont : ContinuousOn (profileEta f F) V := by
    simpa only [profileEta] using
      (continuousOn_id.mul hKderCont).div hMCont
        (fun r hr => ne_of_gt (hMpos r hr))
  have hYCont : ContinuousOn (profileY F) V := by
    simpa only [profileY] using
      continuousOn_const.sub
        ((continuousOn_id.mul hFderCont).div hFCont
          (fun r hr => ne_of_gt (hFpos r hr)))
  have hTCont : ContinuousOn (profileT F) V := by
    simpa only [profileT] using continuousOn_id.mul hFCont
  have hMexpr : ContinuousOn
      (fun r => profileK f F r ^ 2 - 1) V :=
    (hKCont.pow 2).sub continuousOn_const
  have hcontact : ContinuousOn
      (fun r => contactResidual r (profileT F r) (profileY F r)
        (profileK f F r ^ 2 - 1) (profileEta f F r)) V := by
    dsimp only [contactResidual]
    exact (((((continuousOn_id.pow 2).add
      (hMexpr.mul (hTCont.pow 2))).sub
      (continuousOn_const.mul hYCont)).sub
      (continuousOn_const.mul (hYCont.pow 2))).sub
      (hEtaCont.pow 2))
  have hweight : ContinuousOn (piconeWeightFromProfiles f F) V := by
    simpa only [piconeWeightFromProfiles] using
      ((hfCont.pow 2).sub (hFCont.pow 2)).div
        (continuousOn_id.pow 2)
        (fun r hr => pow_ne_zero 2 (ne_of_gt hr.1))
  simpa only [profilePiconeRemainder] using
    (((continuousOn_id.pow m).mul hweight).mul hcontact).mul
      (hbCont.pow 2)

end

end BrezisOP6
