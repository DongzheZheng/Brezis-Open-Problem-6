# Reproducibility record

The project is pinned to Lean 4.29.0 and mathlib v4.29.0. Its released source passed a full build on a remote server. The library target builds the modules under `BrezisOP6/`; the root module is then compiled explicitly to refresh the aggregate `.olean` before the axiom audit.

```text
lake build BrezisOP6               completed successfully (8545 jobs)
lake env lean -o .lake/build/lib/lean/BrezisOP6.olean BrezisOP6.lean
                                    exit code 0
lake env lean AxiomAudit.lean       exit code 0
```

`AxiomAudit.lean` prints the kernel axioms of representative steps and public endpoints. In particular, the following checks each printed only `[propext, Classical.choice, Quot.sound]`:

- `physical_weak_fixed_trace_strong_closure`
- `actual_smooth_annular_energy_gap_uniform`
- `physical_weak_ball_minimum_and_ae_equality`
- `physicalWeakUnitBase_eq_vortex_on_unitBall`
- `physical_weak_unit_epsilon_minimum_and_ae_equality`
- `profileYZeroExtension_differentiable`
- `PhysicalRadialDataCore.f_origin_coefficients`
- `PhysicalRadialDataCore.F_origin_coefficients`
- `PhysicalRadialDataCore.toPhysicalRadialData`
- `C1FixedTraceZeroExtensionApproximation.ballEnergyClosure`
- `publishedC1_and_standardTrace_to_ballMinimality`
- `physical_weak_ball_minimum_and_ae_equality_from_core`
- `physical_weak_unit_epsilon_minimum_and_ae_equality_from_core`
- `physical_weak_unit_base_from_core_ae_eq_vortex`

A source scan found no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration in `BrezisOP6/` or `vendor/`. The vendored DeGiorgi files, their upstream commit, and Apache-2.0 license are recorded in [`vendor/DeGiorgi/README.md`](vendor/DeGiorgi/README.md). Reproduce the checks with:

```sh
lake build BrezisOP6
lake env lean -o .lake/build/lib/lean/BrezisOP6.olean BrezisOP6.lean
lake env lean AxiomAudit.lean
python3 scripts/source_digest.py
```

These checks verify the Lean proof chain **under the four displayed analytic hypotheses**. [`EXTERNAL_INPUTS.md`](EXTERNAL_INPUTS.md) records their mathematical sources, their exact interfaces, and the standard trace/zero-extension identification. The radial-profile and whole-space vortex-minimality inputs are established results specific to this problem; the sphere gap and trace theorem are classical background. Their proofs are external to this Lean project. The known two-dimensional theorem is outside its scope.
