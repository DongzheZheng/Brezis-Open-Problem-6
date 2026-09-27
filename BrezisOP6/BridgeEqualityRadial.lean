import BrezisOP6.BridgeEqualityIntegral

/-!
# Rigidity of the radial variance at bridge equality

Strict profile separation makes the coefficient of the radial mean-zero
variance positive at every interior radius.  Hence the almost-everywhere
vanishing furnished by the integrated equality theorem removes the weight.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem radial_meanZero_derivative_zero_ae_of_weighted_zero
    (m : ℕ) (e : H) (d : ℝ → ℝ) (dv : ℝ → H)
    (dc : ℝ → ℝ) (R : ℝ)
    (hdpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < d r)
    (hweighted : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) R)),
      r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2 = 0) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      dv r = dc r • e := by
  have hSub : Ioo (0 : ℝ) R ⊆ Ioc 0 R := by
    intro r hr
    exact ⟨hr.1, hr.2.le⟩
  have hw : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      r ^ (m + 2) * d r * ‖dv r - dc r • e‖ ^ 2 = 0 :=
    ae_restrict_of_ae_restrict_of_subset hSub hweighted
  filter_upwards [hw, ae_restrict_mem measurableSet_Ioo] with r hz hr
  have hfac : 0 < r ^ (m + 2) * d r :=
    mul_pos (pow_pos hr.1 _) (hdpos r hr)
  have hsq : ‖dv r - dc r • e‖ ^ 2 = 0 := by
    have hz' : (r ^ (m + 2) * d r) *
        ‖dv r - dc r • e‖ ^ 2 = 0 := by
      simpa only [mul_assoc] using hz
    exact (mul_eq_zero.mp hz').resolve_left hfac.ne'
  have hnorm : ‖dv r - dc r • e‖ = 0 := by
    nlinarith [norm_nonneg (dv r - dc r • e)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- For a `C¹` radial Hilbert family, almost-everywhere vanishing of the
mean-zero derivative implies that the mean-zero trace is constant across
the connected open radial interval. -/
theorem radial_meanZero_part_constant_on_open
    (e : H) (v dv : ℝ → H) (c dc : ℝ → ℝ) (R : ℝ)
    (hv : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt v (dv r) r)
    (hc : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt c (dc r) r)
    (hcont : ContinuousOn (fun r => dv r - dc r • e) (Ioo 0 R))
    (hzero : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      dv r = dc r • e)
    (r s : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
    (hs : s ∈ Ioo (0 : ℝ) R) :
    v r - c r • e = v s - c s • e := by
  let h : ℝ → H := fun t => v t - c t • e
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      HasDerivAt h (dv t - dc t • e) t := by
    simpa only [h] using (hv t ht).sub ((hc t ht).smul_const e)
  have hAE : (fun t => dv t - dc t • e) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) R)] (fun _ => 0) := by
    filter_upwards [hzero] with t ht
    simp [ht]
  have hzeroOn : ∀ t ∈ Ioo (0 : ℝ) R,
      dv t - dc t • e = 0 := by
    have hEqOn : Set.EqOn (fun t => dv t - dc t • e)
        (fun _ => 0) (Ioo (0 : ℝ) R) :=
      Measure.eqOn_open_of_ae_eq hAE isOpen_Ioo hcont continuousOn_const
    intro t ht
    exact hEqOn ht
  have hdiff : DifferentiableOn ℝ h (Ioo (0 : ℝ) R) := by
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hderivZero : Set.EqOn (deriv h) (fun _ => 0)
      (Ioo (0 : ℝ) R) := by
    intro t ht
    rw [(hderiv t ht).deriv, hzeroOn t ht]
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    hdiff hderivZero hr hs

/-- A left limit identifies an interior radial constant with its outer
boundary value.  This is where the actual boundary trace enters equality. -/
theorem radial_constant_eq_outer_of_left_limit
    (h : ℝ → H) (R : ℝ) (hR : 0 < R)
    (hconst : ∀ r ∈ Ioo (0 : ℝ) R,
      ∀ s ∈ Ioo (0 : ℝ) R, h r = h s)
    (hlim : Tendsto h (𝓝[<] R) (𝓝 (h R)))
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    h r = h R := by
  have hpos : ∀ᶠ s in 𝓝[<] R, 0 < s :=
    (eventually_gt_nhds hR).filter_mono nhdsWithin_le_nhds
  have hlt : Iio R ∈ 𝓝[<] R := self_mem_nhdsWithin
  have hevent : h =ᶠ[𝓝[<] R] (fun _ : ℝ => h r) := by
    filter_upwards [hpos, hlt] with s hs0 hsR
    exact hconst s ⟨hs0, hsR⟩ r hr
  have hconstLim : Tendsto h (𝓝[<] R) (𝓝 (h r)) :=
    (tendsto_congr' hevent.symm).1 tendsto_const_nhds
  exact tendsto_nhds_unique hconstLim hlim

end

end BrezisOP6
