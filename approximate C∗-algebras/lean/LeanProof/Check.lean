import LeanProof

/-! Axiom audit: every result below should depend only on `propext`, `Classical.choice`,
`Quot.sound` (Lean's standard axioms). In particular no `sorryAx`, and Kitaev's
finite-dimensional theorem enters only as the explicit hypothesis `KitaevFiniteDim`. -/

#print axioms Kitaev.ofCStarAlgebra
#print axioms Kitaev.DeltaIso.symm
#print axioms Kitaev.lpEpsCStar
#print axioms Kitaev.lpDeltaIso
#print axioms Kitaev.sectors_of_kitaev
#print axioms Kitaev.Graded.graded_rigidity

#check @Kitaev.sectors_of_kitaev
#check @Kitaev.Graded.graded_rigidity
