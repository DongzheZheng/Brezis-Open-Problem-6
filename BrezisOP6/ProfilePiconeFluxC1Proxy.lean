import BrezisOP6.SphereActualC1Proxy
import BrezisOP6.ProfilePiconeRemainderMeasurable

/-!
# C¹ regularity of the Picone boundary flux on a positive annulus

The multiplier cancels from the Picone boundary term wherever it is
positive. The remaining origin factor uses only first profile derivatives,
so C² radial profiles make its flux C¹ on every regular annulus.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem profilePiconeOriginFactor_contDiffOn
    (f F : ℝ → ℝ) (U : Set ℝ) (hUopen : IsOpen U)
    (hfC2 : ContDiff ℝ 2 f) (hFC2 : ContDiff ℝ 2 F)
    (hrne : ∀ r ∈ U, r ≠ 0)
    (hFne : ∀ r ∈ U, F r ≠ 0)
    (hMne : ∀ r ∈ U, profileM f F r ≠ 0) :
    ContDiffOn ℝ 1 (profilePiconeOriginFactor f F) U := by
  have hfC1 : ContDiff ℝ 1 f := hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 F := hFC2.of_le (by norm_num)
  have hK2 : ContDiffOn ℝ 2 (profileK f F) U := by
    simpa only [profileK] using
      (hfC2.contDiffOn.div hFC2.contDiffOn hFne)
  have hK1 : ContDiffOn ℝ 1 (profileK f F) U :=
    hK2.of_le (by norm_num)
  have hKder : ContDiffOn ℝ 1 (deriv (profileK f F)) U :=
    hK2.deriv_of_isOpen hUopen (by norm_num)
  have hFder : ContDiffOn ℝ 1 (deriv F) U :=
    hFC2.contDiffOn.deriv_of_isOpen hUopen (by norm_num)
  have hM1 : ContDiffOn ℝ 1 (profileM f F) U := by
    simpa only [profileM, ratioM] using
      (hK1.pow 2).sub contDiffOn_const
  have hEta : ContDiffOn ℝ 1 (profileEta f F) U := by
    simpa only [profileEta] using
      (contDiffOn_id.mul hKder).div hM1 hMne
  have hY : ContDiffOn ℝ 1 (profileY F) U := by
    simpa only [profileY] using
      contDiffOn_const.sub
        ((contDiffOn_id.mul hFder).div hFC1.contDiffOn hFne)
  have hW : ContDiffOn ℝ 1 (piconeWeightFromProfiles f F) U := by
    simpa only [piconeWeightFromProfiles] using
      ((hfC1.contDiffOn.pow 2).sub (hFC1.contDiffOn.pow 2)).div
        (contDiffOn_id.pow 2)
        (fun r hr => pow_ne_zero 2 (hrne r hr))
  have hP : ContDiffOn ℝ 1
      (fun r => piconeMultiplierLogSlope
        (profileY F r) (profileK f F r) (profileEta f F r)) U := by
    simpa only [piconeMultiplierLogSlope] using
      (hY.add (hK1.mul hEta)).neg
  simpa only [profilePiconeOriginFactor] using hW.mul hP

end

end BrezisOP6
