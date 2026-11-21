module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Compactness.Compact

/-! # Topology on monoid units -/

@[expose] public section

namespace RiemannMasullo

open Topology

/-- The units of a compact Hausdorff topological monoid form a compact space. -/
theorem compactSpace_units_of_compactSpace (M : Type*) [Monoid M]
    [TopologicalSpace M] [T2Space M] [ContinuousMul M] [CompactSpace M] :
    CompactSpace Mˣ := by
  refine IsClosedEmbedding.compactSpace ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hrange : Set.range (Units.embedProduct M) =
      {p | p.1 * MulOpposite.unop p.2 = 1} ∩ {p | MulOpposite.unop p.2 * p.1 = 1} := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val_inv, u.inv_val⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨p.1, MulOpposite.unop p.2, h, h'⟩, by cases p; rfl⟩
  rw [hrange]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
    continuous_const).inter (isClosed_eq
      ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

/-- If a monoid embeds with closed image, the induced map on units also has closed image.
Both a unit and its inverse must lift to the original monoid. -/
theorem isClosed_range_unitsMap {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace N]
    (f : M →* N) (hf : Function.Injective f) (hc : IsClosed (Set.range f)) :
    IsClosed (Set.range (Units.map f)) := by
  have h : Set.range (Units.map f) = (Units.val ⁻¹' Set.range f) ∩
      (fun u : Nˣ ↦ (u⁻¹ : Nˣ).val) ⁻¹' Set.range f := by
    ext u
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.val, rfl⟩, ⟨a.inv, rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hab : a * b = 1 := hf (by rw [map_mul, ha, hb, map_one]; exact u.val_inv)
      have hba : b * a = 1 := hf (by rw [map_mul, hb, ha, map_one]; exact u.inv_val)
      exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩
  rw [h]
  exact (hc.preimage Units.continuous_val).inter (hc.preimage Units.continuous_coe_inv)

end RiemannMasullo
