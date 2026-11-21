module

public import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.LocallyFinite

public section

open Set Topology

namespace RiemannMasullo

/-- A set contained in no compact set in a paracompact space with compact neighborhoods
contains a sequence visiting each compact set only finitely often. -/
theorem exists_seq_finite_preimage_of_not_subset_compact {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [ParacompactSpace X] {S : Set X}
    (hS : ∀ K : Set X, IsCompact K → ¬ S ⊆ K) :
    ∃ x : ℕ → X, (∀ n, x n ∈ S) ∧ ∀ K : Set X, IsCompact K → (x ⁻¹' K).Finite := by
  classical
  choose K hK hxK using fun x : X ↦ exists_compact_mem_nhds x
  obtain ⟨V, _, hcover, hloc, hVK⟩ :=
    precise_refinement (fun x ↦ interior (K x)) (fun _ ↦ isOpen_interior)
      (iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, mem_interior_iff_mem_nhds.mpr (hxK x)⟩)
  let I := {i | (V i ∩ S).Nonempty}
  have hI : I.Infinite := by
    intro hfin
    apply hS (⋃ i ∈ I, K i) (hfin.isCompact_biUnion fun i _ ↦ hK i)
    intro y hy
    obtain ⟨i, hiy⟩ := iUnion_eq_univ_iff.mp hcover y
    exact mem_iUnion₂.mpr ⟨i, ⟨y, hiy, hy⟩, interior_subset (hVK i hiy)⟩
  let e := hI.natEmbedding I
  choose x hxV hxS using fun n : ℕ ↦ (e n).property
  refine ⟨x, hxS, fun L hL ↦ ?_⟩
  have hloc' := hloc.comp_injective (Subtype.val_injective.comp e.injective)
  exact (hloc'.finite_nonempty_inter_compact hL).subset fun n hn ↦ ⟨x n, hxV n, hn⟩

end RiemannMasullo
