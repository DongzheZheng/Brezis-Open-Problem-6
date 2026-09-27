import BrezisOP6.EnergySmoothBallBridgeInterior
import BrezisOP6.EnergyPointModification
import BrezisOP6.EnergyQuotientNumeratorOrigin

/-!
# Published vortex minimum as a same-boundary ball input

The external whole-space vortex-minimality theorem is applied to a smooth
finite-ball competitor with the same outer trace.  In analysis this ball
statement follows from the published `H₀¹` perturbation inequality and the
standard zero-trace/extension theorem.  The combined published input is
kept as a theorem-valued proposition here; no new OP6 energy comparison is
assumed.  This interface avoids making energy-closure membership an opaque
extra requirement of the authors' finite-ball argument.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- External analytic input: the entire radial vortex minimizes the actual
Ginzburg--Landau energy against every `C¹` competitor on a ball with the
same boundary values.  The quantifier ranges over arbitrary competitors,
not the special quotient fields in the present proof. -/
structure PublishedBallMinimalityForZeroBoundaryC1 (n : ℕ)
    (V : GLEuclidean n → GLEuclidean n) : Prop where
  energy_le : ∀ (_hn : 3 ≤ n) (R : ℝ) (_hR : 0 < R)
    (v : GLEuclidean n → GLEuclidean n),
    ContDiffOn ℝ 1 v (Metric.closedBall (0 : GLEuclidean n) R) →
    (∀ x : GLEuclidean n, ‖x‖ = R → v x = V x) →
      euclideanBallEnergy n R V ≤ euclideanBallEnergy n R v

/-- Two proved single-profile identities plus the external same-boundary
vortex minimum give the actual finite-ball bridge inequality. -/
theorem euclideanBall_energy_gap_ge_bridge_of_boundaryC1
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hf : SmoothProfileBallInteriorData m f z R ρf Bf)
    (hF : SmoothProfileBallInteriorData m F z R ρF BF)
    (hunit : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hvC1 : ContDiffOn ℝ 1 (fun x => F ‖x‖ • z x)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hvTrace : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      F ‖x‖ • z x = radialVortex (m + 3) F x) :
    (∫ x, bridgeEnergyDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => f ‖y‖)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) ≤
      euclideanBallEnergy (m + 3) R (fun x => f ‖x‖ • z x) -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) f) := by
  let μ : Measure (GLEuclidean (m + 3)) :=
    volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)
  have hfInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R f z hf.reduced_density_integrable
  have hFInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R F z hF.reduced_density_integrable
  have hfIdentity := smooth_openBall_singleProfile_identity_interior
    m f z R ρf Bf hf hunit
  have hFIdentity := smooth_openBall_singleProfile_identity_interior
    m F z R ρF BF hF hunit
  have hbridge := finiteBall_energy_bridge μ
    (euclideanGradientSq (m + 3)) (m + 3)
    (fun x => f ‖x‖ • z x) (radialVortex (m + 3) f)
    (fun x => F ‖x‖ • z x) (radialVortex (m + 3) F)
    (fun y => f ‖y‖) (fun y => F ‖y‖)
    (euclideanGradientSq (m + 3) z)
    (fun y => ‖z y‖ ^ 2) (fun y => ‖y‖⁻¹ ^ 2)
    hfInt hFInt
    (by simpa only [glEnergy_eq_euclideanBallEnergy] using hfIdentity)
    (by simpa only [glEnergy_eq_euclideanBallEnergy] using hFIdentity)
  have hmin := hPublished.energy_le (by omega : 3 ≤ m + 3)
    R hR (fun x => F ‖x‖ • z x) hvC1 hvTrace
  simp only [μ, glEnergy_eq_euclideanBallEnergy] at hbridge
  linarith

/-- The actual transformed field may have a removable point at the origin.
Apply the published minimum to a `C¹` representative and transfer the
energy back using the proved null-point invariance, which also accounts
for the Fréchet-gradient term. -/
theorem euclideanBall_energy_gap_ge_bridge_of_C1_representative
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hf : SmoothProfileBallInteriorData m f z R ρf Bf)
    (hF : SmoothProfileBallInteriorData m F z R ρF BF)
    (hunit : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hvOff : ∀ x : GLEuclidean (m + 3), x ≠ 0 →
      v x = F ‖x‖ • z x)
    (hvC1 : ContDiffOn ℝ 1 v
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hvTrace : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      v x = radialVortex (m + 3) F x) :
    (∫ x, bridgeEnergyDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => f ‖y‖)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) ≤
      euclideanBallEnergy (m + 3) R (fun x => f ‖x‖ • z x) -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) f) := by
  let μ : Measure (GLEuclidean (m + 3)) :=
    volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)
  have hfInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R f z hf.reduced_density_integrable
  have hFInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R F z hF.reduced_density_integrable
  have hfIdentity := smooth_openBall_singleProfile_identity_interior
    m f z R ρf Bf hf hunit
  have hFIdentity := smooth_openBall_singleProfile_identity_interior
    m F z R ρF BF hF hunit
  have hbridge := finiteBall_energy_bridge μ
    (euclideanGradientSq (m + 3)) (m + 3)
    (fun x => f ‖x‖ • z x) (radialVortex (m + 3) f)
    (fun x => F ‖x‖ • z x) (radialVortex (m + 3) F)
    (fun y => f ‖y‖) (fun y => F ‖y‖)
    (euclideanGradientSq (m + 3) z)
    (fun y => ‖z y‖ ^ 2) (fun y => ‖y‖⁻¹ ^ 2)
    hfInt hFInt
    (by simpa only [glEnergy_eq_euclideanBallEnergy] using hfIdentity)
    (by simpa only [glEnergy_eq_euclideanBallEnergy] using hFIdentity)
  have hmin := hPublished.energy_le (by omega : 3 ≤ m + 3)
    R hR v hvC1 hvTrace
  have hvEnergy : euclideanBallEnergy (m + 3) R v =
      euclideanBallEnergy (m + 3) R (fun x => F ‖x‖ • z x) :=
    euclideanBallEnergy_eq_of_eq_off_origin (m + 3)
      (by omega) R v (fun x => F ‖x‖ • z x) hvOff
  simp only [μ, glEnergy_eq_euclideanBallEnergy] at hbridge
  rw [hvEnergy] at hmin
  linarith

/-- Off the removable point, the canonical smooth transformed numerator
has exactly the value used in the two-profile identity. -/
theorem energyQuotientNumerator_eq_profile_quotient_off_origin
    (n : ℕ) (f F : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (hx : x ≠ 0) :
    energyQuotientNumerator n f F α β u x =
      F ‖x‖ • ((f ‖x‖)⁻¹ • u x) := by
  simp only [energyQuotientNumerator, if_neg hx]
  rw [div_eq_mul_inv, smul_smul]

end

end BrezisOP6
