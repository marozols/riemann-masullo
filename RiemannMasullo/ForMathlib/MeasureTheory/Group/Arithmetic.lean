module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.GroupWithZero

/-! # Borel sets in the group of units -/

public section

namespace RiemannMasullo

/-- For a group with zero and continuous inversion away from zero, the measurable space
induced by the units projection is the Borel space of the units topology. -/
theorem borelSpace_units_of_continuousInv₀ (M : Type*) [GroupWithZero M] [TopologicalSpace M]
    [ContinuousInv₀ M] [MeasurableSpace M] [BorelSpace M] : BorelSpace Mˣ := by
  constructor
  change MeasurableSpace.comap Units.val ‹MeasurableSpace M› = _
  rw [Units.isEmbedding_val₀.eq_induced, borel_comap, BorelSpace.measurable_eq (α := M)]

end RiemannMasullo
