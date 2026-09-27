/-
SPDX-License-Identifier: Apache-2.0
Source: Scott N. Armstrong and Julia Kempe, DeGiorgi,
https://github.com/scottnarmstrong/DeGiorgi,
commit 4c1b3077d3782b24065184df4ba59501b2e56fc7.
See vendor/DeGiorgi/LICENSE and vendor/DeGiorgi/README.md.
-/
import Mathlib

/-!
# Common Prelude

This module is the shared prelude for the De Giorgi development.

Policy:

- imports come directly from `Mathlib`;
- declarations in this directory live under `DeGiorgi`;
- shared opens and scoped notations live here so the theorem files stay small.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace DeGiorgi

end DeGiorgi
