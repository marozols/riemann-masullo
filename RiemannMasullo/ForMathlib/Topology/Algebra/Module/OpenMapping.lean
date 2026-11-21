module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.GDelta.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Open mapping for complete first-countable topological vector spaces -/

@[expose] public noncomputable section

open Filter Set Function Topology
open scoped Pointwise Uniformity

namespace RiemannMasullo

/-- A continuous homomorphism from a complete first-countable additive group is open
if the closure of the image of each zero-neighborhood is a zero-neighborhood. -/
theorem isOpenMap_of_closure_image_mem_nhds_zero {G H : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [FirstCountableTopology G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [FirstCountableTopology H] [T2Space H] (f : G →+ H) (hf : Continuous f)
    (h : ∀ U ∈ 𝓝 (0 : G), closure (f '' U) ∈ 𝓝 (0 : H)) : IsOpenMap f := by
  obtain ⟨u, hu, hadd⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero G
  obtain ⟨v, hv⟩ := (𝓝 (0 : H)).exists_antitone_basis
  apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
  apply (hu.toHasBasis.map f).ge_iff.mpr
  intro m _
  -- Shrink the permitted error in the target as well as the corrections in the source.
  let W (n : ℕ) := v n ∩ closure (f '' u (m + n + 2))
  have hW (n : ℕ) : W n ∈ 𝓝 (0 : H) := inter_mem (hv.mem n) (h _ (hu.mem _))
  refine mem_of_superset (hW 0) fun y hy ↦ ?_
  have step (n : ℕ) (z : G) (hz : y - f z ∈ W n) :
      ∃ a ∈ u (m + n + 2), y - f (z + a) ∈ W (n + 1) := by
    let r := y - f z
    have hn : {s : H | r - s ∈ W (n + 1)} ∈ 𝓝 r :=
      (continuous_const.sub continuous_id).tendsto' r 0 (sub_self r) (hW _)
    obtain ⟨_, ht, a, ha, rfl⟩ := (mem_closure_iff_nhds.mp hz.2) _ hn
    change y - f z - f a ∈ W (n + 1) at ht
    exact ⟨a, ha, by simpa only [map_add, sub_add_eq_sub_sub] using ht⟩
  let z : (n : ℕ) → {x : G // y - f x ∈ W n} := fun n ↦ Nat.recOn n
    ⟨0, by simpa using hy⟩ fun k zk ↦
      ⟨zk.val + (step k zk.val zk.property).choose, (step k zk.val zk.property).choose_spec.2⟩
  have hstep (n : ℕ) : (z (n + 1)).val - (z n).val ∈ u (m + n + 2) := by
    change (z n).val + (step n (z n).val (z n).property).choose - (z n).val ∈ _
    simpa only [add_sub_cancel_left] using (step n (z n).val (z n).property).choose_spec.1
  -- All later partial sums lie in a single translate of a shrinking neighborhood.
  have hdiff {a b : ℕ} (hab : a ≤ b) : (z b).val - (z a).val ∈ u (m + a + 1) := by
    refine Nat.decreasingInduction' (motive := fun a ↦ (z b).val - (z a).val ∈ u (m + a + 1)) ?_ hab ?_
    · intro k _ _ hk
      exact hadd (m + k + 1) ⟨_, hk, _, hstep k, sub_add_sub_cancel _ _ _⟩
    · simpa only [sub_self] using mem_of_mem_nhds (hu.mem (m + b + 1))
  have hc : CauchySeq (fun n ↦ (z n).val) := by
    have hb : (𝓤 G).HasBasis (fun _ : ℕ ↦ True) fun n ↦ {p : G × G | p.1 - p.2 ∈ u n} := by
      rw [uniformity_eq_comap_nhds_zero_swapped]
      exact hu.toHasBasis.comap _
    exact hb.cauchySeq_iff'.mpr fun n _ ↦
      ⟨n, fun b hb ↦ hu.antitone (by omega : n ≤ m + n + 1) (hdiff hb)⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hmem : x ∈ closure (u (m + 1)) := mem_closure_of_tendsto hx (Eventually.of_forall fun n ↦ by
    simpa only [show (z 0).val = 0 from rfl, sub_zero, Nat.add_zero] using hdiff (Nat.zero_le n))
  refine ⟨x, hadd m ((closure_subset_add_self_of_mem_nhds_zero (hu.mem _)) hmem), ?_⟩
  have hr : Tendsto (fun n ↦ y - f (z n).val) atTop (𝓝 0) := hv.toHasBasis.tendsto_right_iff.mpr
    fun k _ ↦ (eventually_ge_atTop k).mono fun n hn ↦ hv.antitone hn (z n).property.1
  exact (sub_eq_zero.mp
    (tendsto_nhds_unique (tendsto_const_nhds.sub ((hf.tendsto x).comp hx)) hr)).symm

/-- A continuous linear map from a complete first-countable topological vector space to a
first-countable Hausdorff space is open whenever its range is nonmeagre. -/
theorem isOpenMap_of_not_isMeagre_range
    {𝕜 G H : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup G] [Module 𝕜 G]
    [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G] [FirstCountableTopology G]
    [ContinuousSMul 𝕜 G] [AddCommGroup H] [Module 𝕜 H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] [FirstCountableTopology H] [T2Space H] [ContinuousSMul 𝕜 H]
    (f : G →L[𝕜] H) (h : ¬ IsMeagre (range f)) : IsOpenMap f := by
  apply isOpenMap_of_closure_image_mem_nhds_zero f.toLinearMap.toAddMonoidHom f.continuous
  intro U hU
  have hs := (continuous_sub : Continuous (fun p : G × G ↦ p.1 - p.2)).tendsto' (0, 0) 0 (sub_self 0)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp (hs hU)
  let V := P ∩ Q
  have hV : V ∈ 𝓝 (0 : G) := inter_mem hP hQ
  -- Countably many dilations cover the range, so the image of V is somewhere dense.
  have hnon : (interior (closure (f '' V))).Nonempty := by
    by_contra! hd
    have hnd : IsNowhereDense (f '' V) := hd
    obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt 𝕜 zero_lt_one
    let t : 𝕜ˣ := Units.mk0 c (norm_pos_iff.mp hc0)
    let e (n : ℕ) : H ≃ₜ H := Homeomorph.smul ((t ^ n)⁻¹)
    have hcover : range f ⊆ ⋃ n : ℕ, e n '' (f '' V) := by
      rintro _ ⟨x, rfl⟩
      have hsmall : Tendsto (fun n : ℕ ↦ c ^ n • x) atTop (𝓝 0) := by
        simpa only [zero_smul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1).smul_const x
      have hevent : ∀ᶠ n : ℕ in atTop, c ^ n • x ∈ V := hsmall hV
      obtain ⟨n, hn⟩ := hevent.exists
      refine mem_iUnion.mpr ⟨n, f (c ^ n • x), ⟨_, hn, rfl⟩, ?_⟩
      change (t ^ n)⁻¹ • f (c ^ n • x) = f x
      rw [map_smul]
      exact inv_smul_smul (t ^ n) (f x)
    have hm := isMeagre_iUnion fun n ↦ ((e n).isEmbedding.isInducing.isNowhereDense_image hnd).isMeagre
    exact h (hm.mono hcover)
  obtain ⟨z, hz⟩ := hnon
  have hz' : {a : H | a + z ∈ closure (f '' V)} ∈ 𝓝 0 :=
    (continuous_id.add continuous_const).tendsto' 0 z (zero_add z) (mem_interior_iff_mem_nhds.mp hz)
  filter_upwards [hz'] with a ha
  rw [← add_sub_cancel_right a z]
  apply map_mem_closure₂ continuous_sub ha (interior_subset hz)
  rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
  exact ⟨b - d, hPQ (a := (b, d)) ⟨hb.1, hd.2⟩, map_sub f b d⟩

end RiemannMasullo
