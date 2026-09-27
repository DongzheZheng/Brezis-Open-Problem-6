import BrezisOP6.SphereActualMeanRightLimit
import BrezisOP6.BridgeFluxRightEndpoint
import BrezisOP6.OriginTaylorInterior

/-!
# Origin flux for the actual finite-ball spherical zero mode

The zero mode is defined by totalization at radius zero.  Its assigned
value there is irrelevant: the finite right trace, together with the
profile slopes, makes the integration-by-parts flux vanish at the origin.
-/

namespace BrezisOP6

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem actual_finiteBallSphereRadialMean_flux_right_limit
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F H : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (α β Af Bf AF BF : ℝ)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hH : ContinuousAt H 0) (hH0 : H 0 ≠ 0)
    (hu : ContinuousAt u 0)
    (hf : ∀ s : ℝ, 0 < s → s ≤ R →
      f s = s * H (s ^ 2))
    (hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s)
    (hz : ContDiffOn ℝ 1
      (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (i : Fin (m + 3)) :
    Tendsto
      (bridgeOriginFlux m f F
        (vectorSphereRadialMean (m + 3)
          (finiteBallSphereFamily (m + 3) R
            (fun x => (f ‖x‖)⁻¹ • u x))
          (fun s k => finiteBallSphereFamily_memLp (m + 3) R
            (fun x => (f ‖x‖)⁻¹ • u x) hz s k) i))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨B, hb⟩ := actual_finiteBallSphereRadialMean_right_limit
    (m + 3) R hR f H u hH hH0 hu hf hfpos hz i
  exact bridgeOriginFlux_tendsto_zero_of_right_limit
    m f F _ α β B
    (profile_div_radius_origin_limit (hfTaylor.toGlobal hR))
    (profile_div_radius_origin_limit (hFTaylor.toGlobal hR)) hb

end

end BrezisOP6
