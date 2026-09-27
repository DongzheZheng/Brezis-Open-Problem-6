# Brezis’ Open Problem 6: a Lean 4 formalization of the higher-dimensional argument

Consider the degree-one Dirichlet problem on the unit ball $B^n\subset\mathbb R^n$:

$$
E_\varepsilon(u)=\int_{B^n}\left(\frac12|\nabla u|^2+
  \frac{(1-|u|^2)^2}{4\varepsilon^2}\right)\,dx,
\qquad u|_{\partial B^n}(\omega)=\omega.
$$

For every $n\ge3$ and $\varepsilon>0$, the main Lean theorem proves that the radial vortex $U_\varepsilon(x)=f_\varepsilon(|x|)x/|x|$ minimizes this **actual Ginzburg–Landau energy** and that equality forces $u=U_\varepsilon$ almost everywhere. The theorem covers weak finite-energy competitors with the prescribed trace. It is proved under four explicit, established analytic inputs listed below; the comparison, stability, weak-limit, and scaling arguments that take those inputs to the conclusion are formalized in Lean.

The public endpoint is [`physical_weak_unit_epsilon_minimum_and_ae_equality_from_core`](BrezisOP6/PhysicalWeakCanonicalYMain.lean). Its companion `physical_weak_ball_minimum_and_ae_equality_from_core` treats a ball of arbitrary positive radius at unit coupling. The dimension is represented as $n=m+3$, with $m:\mathbb N$.

## The proof in Lean

The development constructs the auxiliary profile slope defect and its regular extension at the origin, then proves strict profile comparison and the first-contact barrier. A Picone identity controls the radial mode, while the sharp spherical gap controls the remaining modes. These estimates feed an identity for the Euclidean energy and a quantitative energy gap on every compact annulus, with a constant fixed before the competitor is chosen. Strong $H^1\cap L^4$ approximation transfers the comparison and equality statement to weak fixed-trace fields. Finally, a weak-gradient change of scale yields the unit-ball statement for every positive $\varepsilon$.

The formal weak class [`WeakFixedTraceCompetitor`](BrezisOP6/WeakBallEnergy.lean) uses distributional gradients. The difference $u-U_\varepsilon$, extended by zero, has a global weak gradient and lies in $H^1\cap L^4$. On a smooth ball this is the standard zero-trace description of the fixed-boundary class; the trace identification is part of the cited Sobolev background. The $L^4$ condition records the integrability of the quartic potential in all dimensions, including $n\ge5$.

## Analytic inputs

The final theorem takes these four mathematical facts as separate Lean hypotheses. Their proofs are supplied by the cited literature or classical analysis; they are not asserted as custom Lean axioms or claimed to be formalized here.

| Input in the Lean theorem | Mathematical content and source |
| --- | --- |
| [`PhysicalRadialDataCore`](BrezisOP6/PhysicalProfileYExtension.lean) | Finite-ball and entire-space radial profiles, their ODE, boundary and far-field behavior, strict increase, and regular-origin factorization. Profile existence and monotonicity follow the results of [Ignat–Nguyen–Slastikov–Zarnescu (2014)](https://doi.org/10.1137/130948598); the regular-origin factorization also uses classical analytic elliptic regularity (compare [Morrey (1958)](https://doi.org/10.2307/2372830)). Lean derives the needed origin coefficients and slope-defect properties from this interface. |
| [`PublishedC1VortexMinimality`](BrezisOP6/EnergyAdmissibility.lean) | The entire radial vortex minimizes against arbitrary compactly supported $C^1$ perturbations: [Millot–Pisante (2010)](https://doi.org/10.4171/JEMS/223) for $n=3$, and [Pisante (2011)](https://doi.org/10.1016/j.jfa.2010.09.002) for higher dimensions. |
| [`StandardC1FixedTraceZeroExtensionBridge`](BrezisOP6/PublishedC1TraceBridge.lean) | The classical Sobolev zero-trace and density result that transfers the compact-test comparison to smooth same-boundary fields. Lean proves the resulting strong-convergence energy limit and the ball comparison. |
| [`SharpUnitSpherePoincareLocal`](BrezisOP6/SphereLocalPoincare.lean) | The classical sharp scalar Poincaré inequality on $S^{n-1}$, with first positive eigenvalue $n-1$. |

The first two entries are established, problem-specific theorems; the latter two are classical spectral and Sobolev facts. The exact formal interfaces, including the regularity representatives used for radial profiles and the zero-extension formulation of fixed trace, are documented in [`EXTERNAL_INPUTS.md`](EXTERNAL_INPUTS.md). The known two-dimensional case is outside the scope of this Lean development.

## Reproduce the verification

The project pins **Lean 4.29.0** and **mathlib v4.29.0** in [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json). With `elan` and `lake` installed, run from the repository root:

```sh
lake build BrezisOP6
lake env lean -o .lake/build/lib/lean/BrezisOP6.olean BrezisOP6.lean
lake env lean AxiomAudit.lean
```

The separate root-module command refreshes the aggregate `.olean` used by the audit. [`AxiomAudit.lean`](AxiomAudit.lean) inspects representative theorems with `#print axioms`; the public endpoints report only Lean's logical axioms `propext`, `Classical.choice`, and `Quot.sound`. The source contains no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration. This kernel check validates the proofs **under the four stated hypotheses**. See the [verification record](VERIFICATION.md) for the completed build and the [theorem map](PAPER_FORMALIZATION_MAP.zh-CN.md) for the detailed correspondence.

## Repository guide

| Path | Contents |
| --- | --- |
| [`BrezisOP6/PhysicalWeakCanonicalYMain.lean`](BrezisOP6/PhysicalWeakCanonicalYMain.lean) | Public weak finite-ball and all-$\varepsilon$ unit-ball theorems. |
| [`BrezisOP6/`](BrezisOP6/) | Profile comparison, Picone and spherical estimates, physical energy identities, annular stability, weak closure, and scaling. |
| [`AxiomAudit.lean`](AxiomAudit.lean) | Kernel-axiom checks for the main proof chain. |
| [`EXTERNAL_INPUTS.md`](EXTERNAL_INPUTS.md), [`PAPER_FORMALIZATION_MAP.zh-CN.md`](PAPER_FORMALIZATION_MAP.zh-CN.md), [`VERIFICATION.md`](VERIFICATION.md) | Mathematical dependencies, theorem correspondence, and reproducibility record. |
| [`vendor/DeGiorgi/`](vendor/DeGiorgi/) | Credited Sobolev approximation modules. Their exact upstream commit and Apache-2.0 license are recorded in the [vendor notice](vendor/DeGiorgi/README.md). |
