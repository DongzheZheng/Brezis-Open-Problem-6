import BrezisOP6.WeakAnnularEqualityLimit

/-!
# Axiom audit for the weak annular limit

The quantitative smooth annular estimate and fixed-trace density occur as
explicit theorem parameters.  These commands check that the limit argument
itself does not introduce further axioms.
-/

#print axioms BrezisOP6.ae_eq_on_set_of_strongL2_and_gap_stability
#print axioms BrezisOP6.ae_eq_of_annular_ae_eq
#print axioms BrezisOP6.weak_ae_eq_of_strong_closure_and_smooth_annular_stability
#print axioms BrezisOP6.weak_minimum_and_ae_equality_of_strong_closure_and_annular_stability
