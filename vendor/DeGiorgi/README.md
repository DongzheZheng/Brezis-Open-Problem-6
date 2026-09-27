# Vendored Sobolev approximation modules

These six Lean source files are excerpted from Scott N. Armstrong and Julia
Kempe's [DeGiorgi formalization](https://github.com/scottnarmstrong/DeGiorgi),
commit `4c1b3077d3782b24065184df4ba59501b2e56fc7`.
They are licensed under Apache-2.0; see [LICENSE](LICENSE). The source files
are used to prove scalar weak-derivative witnesses and smooth Sobolev
approximation for the OP6 formalization. Their original `DeGiorgi` namespace
and source structure are retained.

The only mathematical additions to the upstream sources are
`exists_smooth_compactSupport_W1p_L4_approx_univ` and
`exists_smooth_W1p_L4_approx_inside_open`, appended to
`SobolevSpace/Approximation.lean`. The first records convergence in `L⁴`
for the **same** explicit mollifier sequence as the upstream `W¹,p`
approximation. The second uses the positive support clearance to keep its
approximants inside a prescribed open set. Both adapt the nearby upstream
proofs and remain under Apache-2.0.

The OP6-specific vector-valued interface is in
`BrezisOP6/WeakToDeGiorgi.lean`, outside this vendor directory.
