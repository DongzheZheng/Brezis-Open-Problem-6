import BrezisOP6.OriginFluxFactor
import BrezisOP6.BridgePiconeIdentificationInterior

/-!
# Right endpoint for the bridge's elementary integration-by-parts flux

The actual regularized mean need not be continuous at its totalized value
at zero.  Its finite right limit is sufficient because the bridge flux
contains the vanishing factor `r^(m+1)`.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

theorem profilePiconeWeight_tendsto_origin
    {f F : ℝ → ℝ} {α β : ℝ}
    (hf : Tendsto (fun r => f r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 β))
    (hF : Tendsto (fun r => F r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 α)) :
    Tendsto (piconeWeightFromProfiles f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (β ^ 2 - α ^ 2)) := by
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      piconeWeightFromProfiles f F r =
        (f r / r) ^ 2 - (F r / r) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hrpos
    have hr : 0 < r := hrpos
    unfold piconeWeightFromProfiles
    field_simp [ne_of_gt hr]
  exact (tendsto_congr' heq).2 ((hf.pow 2).sub (hF.pow 2))

theorem bridgeOriginFlux_tendsto_zero_of_right_limit
    (m : ℕ) (f F b : ℝ → ℝ) (α β B : ℝ)
    (hf : Tendsto (fun r => f r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 β))
    (hF : Tendsto (fun r => F r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 α))
    (hb : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    Tendsto (bridgeOriginFlux m f F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  simpa only [bridgeOriginFlux] using
    zeroMode_origin_flux_tendsto_of_one_sided m
      (profilePiconeWeight_tendsto_origin hf hF) hb

end

end BrezisOP6
