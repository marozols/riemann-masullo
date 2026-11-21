module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.UrysohnsLemma

public section

open Filter Set TopologicalSpace Topology
open scoped CompactlySupported

namespace RiemannMasullo

/-- Compactly supported maps are dense for the compact-open topology when the target
admits a continuous real scalar action with zero. -/
theorem denseRange_toContinuousMap_of_real_smul {X E : Type*} [TopologicalSpace X]
    [R1Space X] [LocallyCompactSpace X] [Zero E] [TopologicalSpace E]
    [MulActionWithZero ℝ E] [ContinuousSMul ℝ E] :
    DenseRange (CompactlySupportedContinuousMap.toContinuousMap : C_c(X, E) → C(X, E)) := by
  intro f
  have approx (K : Compacts X) : ∃ g : C_c(X, E), EqOn g f K := by
    obtain ⟨φ, hφ, hcomp, _, _⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen K.isCompact isOpen_univ (subset_univ _)
    refine ⟨⟨⟨fun x ↦ φ x • f x, φ.continuous.smul f.continuous⟩,
      (show HasCompactSupport (φ : X → ℝ) from hcomp).smul_right⟩, ?_⟩
    intro x hx
    change φ x • f x = f x
    rw [hφ hx, Pi.one_apply, one_smul]
  choose g hg using approx
  apply mem_closure_of_tendsto (f := fun K ↦ (g K).toContinuousMap) (b := atTop)
  · apply ContinuousMap.tendsto_nhds_compactOpen.mpr
    intro L hL U _ hU
    filter_upwards [eventually_ge_atTop (⟨L, hL⟩ : Compacts X)] with K hLK x hx
    change g K x ∈ U
    rw [hg K (hLK hx)]
    exact hU hx
  · exact Eventually.of_forall fun K ↦ mem_range_self (g K)

end RiemannMasullo
