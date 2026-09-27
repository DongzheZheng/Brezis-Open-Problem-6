import BrezisOP6.EnergyQuotientFluxEnvelope
import BrezisOP6.OriginFluxFactor

/-!
# The quotient competitor's numerator at the radial origin

Two regular-origin radial profiles have a finite quotient limit equal to the
ratio of their initial slopes. Consequently multiplying this quotient by a
competitor continuous at the origin gives a continuous numerator extension.
The denominator is also explicitly nonzero on a punctured neighborhood.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

/-- On a small positive interval a profile with positive initial slope
does not vanish. The conclusion is obtained from its Taylor limit. -/
theorem profile_ne_zero_near_origin_of_taylor
    {f : ℝ → ℝ} {β Af Bf R : ℝ}
    (hR : 0 < R) (hβ : 0 < β)
    (hf : RadialOriginTaylorOn f β Af Bf R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r, 0 < r → r < δ → f r ≠ 0 := by
  have hlim := profile_div_radius_origin_limit (hf.toGlobal hR)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < f r / r :=
    hlim.eventually (eventually_gt_nhds hβ)
  obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hpos
  refine ⟨δ, hδpos, ?_⟩
  intro r hr hrδ
  have hfr : 0 < f r :=
    (div_pos_iff_of_pos_right hr).mp (hδ ⟨hr, hrδ⟩)
  exact ne_of_gt hfr

/-- The numerator `w_F=(F/f)u` with its removable value at the origin. -/
def energyQuotientNumerator (n : ℕ) (f F : ℝ → ℝ)
    (α β : ℝ) (u : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) : GLEuclidean n :=
  if x = 0 then (α / β) • u 0 else (F ‖x‖ / f ‖x‖) • u x

/-- The radial quotient has its expected continuous extension at zero,
and its denominator is nonzero on a punctured ball. -/
theorem energyQuotientNumerator_origin_regular
    (n : ℕ) (f F : ℝ → ℝ) (u : GLEuclidean n → GLEuclidean n)
    (α β Af Bf AF BF R : ℝ)
    (hR : 0 < R) (hβ : 0 < β)
    (hf : RadialOriginTaylorOn f β Af Bf R)
    (hF : RadialOriginTaylorOn F α AF BF R)
    (hu : ContinuousAt u 0) :
    (∃ δ : ℝ, 0 < δ ∧
      ∀ x : GLEuclidean n, x ≠ 0 → ‖x‖ < δ → f ‖x‖ ≠ 0) ∧
      ContinuousAt (energyQuotientNumerator n f F α β u) 0 := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    profile_ne_zero_near_origin_of_taylor hR hβ hf
  have hdenom : ∃ δ : ℝ, 0 < δ ∧
      ∀ x : GLEuclidean n, x ≠ 0 → ‖x‖ < δ → f ‖x‖ ≠ 0 := by
    refine ⟨δ, hδpos, ?_⟩
    intro x hx hxδ
    exact hδ ‖x‖ (norm_pos_iff.mpr hx) hxδ
  have hquot : Tendsto (fun r => F r / f r)
      (𝓝[>] (0 : ℝ)) (𝓝 (α / β)) := by
    simpa only [profileK] using
      (profileK_origin_limit hβ (hF.toGlobal hR) (hf.toGlobal hR))
  have hnorm : Tendsto (fun x : GLEuclidean n => ‖x‖)
      (𝓝[≠] (0 : GLEuclidean n)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun x : GLEuclidean n => ‖x‖) 0 := by
        fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hxne : x ≠ 0 := by simpa using hx
      exact norm_pos_iff.mpr hxne
  have hqnorm : Tendsto
      (fun x : GLEuclidean n => F ‖x‖ / f ‖x‖)
      (𝓝[≠] (0 : GLEuclidean n)) (𝓝 (α / β)) :=
    hquot.comp hnorm
  have huPunct : Tendsto u (𝓝[≠] (0 : GLEuclidean n)) (𝓝 (u 0)) :=
    hu.tendsto.mono_left nhdsWithin_le_nhds
  have hsmul := hqnorm.smul huPunct
  have heq : (energyQuotientNumerator n f F α β u) =ᶠ[
      𝓝[≠] (0 : GLEuclidean n)]
      (fun x => (F ‖x‖ / f ‖x‖) • u x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : x ≠ 0 := by simpa using hx
    simp [energyQuotientNumerator, hxne]
  refine ⟨hdenom, ?_⟩
  rw [continuousAt_iff_punctured_nhds]
  simpa only [energyQuotientNumerator, if_pos rfl] using
    (tendsto_congr' heq).2 hsmul

end

end BrezisOP6
