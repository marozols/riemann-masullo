module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-! # The trivial complex character of a compact monoid -/

@[expose] public section

namespace RiemannMasullo

open Filter

/-- A complex-valued homomorphism with compact range inside the open unit ball about one
is trivial. -/
theorem monoidHom_eq_one_of_compact_range_subset_ball {G : Type*} [Monoid G]
    (q : G →* ℂ) (hK : IsCompact (Set.range q))
    (hq : Set.range q ⊆ Metric.ball 1 1) : q = 1 := by
  have hdist : Continuous (fun z : ℂ => ‖z - 1‖) :=
    (continuous_id.sub continuous_const).norm
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hK.exists_isMaxOn ⟨1, ⟨1, map_one q⟩⟩ hdist.continuousOn
  have hbound (y : G) : ‖q y - 1‖ ≤ ‖q x - 1‖ := hx (Set.mem_range_self y)
  have hclose : ‖q x - 1‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hq (Set.mem_range_self x)
  have hfactor : 1 < ‖q x + 1‖ := by
    have h := norm_add_le (q x + 1) (1 - q x)
    have hsum : q x + 1 + (1 - q x) = 2 := by ring
    rw [hsum, norm_sub_rev, Complex.norm_ofNat] at h
    linarith
  -- Squaring would increase the maximum distance from one if it were positive.
  have hsq := hbound (x ^ 2)
  have hsq_factor : q x ^ 2 - 1 = (q x + 1) * (q x - 1) := by ring
  rw [map_pow, hsq_factor, norm_mul] at hsq
  have hzero : ‖q x - 1‖ = 0 := by
    nlinarith [norm_nonneg (q x - 1)]
  ext y
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm ((hbound y).trans_eq hzero) (norm_nonneg _)))

/-- The trivial complex character of a compact monoid is isolated in the compact-open topology. -/
theorem isOpen_singleton_one_complex {G : Type*} [Monoid G] [TopologicalSpace G] [CompactSpace G] :
    IsOpen ({1} : Set (G →ₜ* ℂ)) := by
  let V : Set (G →ₜ* ℂ) := {c | Set.MapsTo c Set.univ (Metric.ball 1 1)}
  have hV : IsOpen V := isOpen_induced
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ Metric.isOpen_ball)
  have hVeq : V = {1} := by
    ext c
    rw [Set.mem_singleton_iff]
    refine ⟨fun hc ↦ ?_, ?_⟩
    · have h := monoidHom_eq_one_of_compact_range_subset_ball c.toMonoidHom
        (isCompact_range c.continuous) (by
          rintro _ ⟨x, rfl⟩
          exact hc (Set.mem_univ x))
      exact ContinuousMonoidHom.ext fun x => DFunLike.congr_fun h x
    · rintro rfl y _
      simp [Metric.mem_ball]
  simpa [hVeq] using hV

open Set Topology in
/-- A continuous complex-valued homomorphism on a product of compact monoids is trivial on
the elements that equal one in some fixed finite set of coordinates. -/
theorem exists_finset_complexCharacter_eq_one {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, CompactSpace (M i)] (c : (∀ i, M i) →ₜ* ℂ) :
    ∃ S : Finset ι, ∀ x : ∀ i, M i, (∀ i ∈ S, x i = 1) → c x = 1 := by
  classical
  have hV : c ⁻¹' Metric.ball 1 1 ∈ 𝓝 1 := c.continuous.continuousAt.preimage_mem_nhds
    (by
      change Metric.ball (1 : ℂ) 1 ∈ 𝓝 (c 1)
      rw [map_one]
      exact Metric.ball_mem_nhds _ zero_lt_one)
  rw [nhds_pi] at hV
  obtain ⟨S, V, hV, hsub⟩ := Filter.mem_pi'.mp hV
  let cut : (∀ i, M i) →* ∀ i, M i :=
    MonoidHom.pi fun i ↦ if i ∈ S then 1 else Pi.evalMonoidHom M i
  have hcut (x : ∀ i, M i) (i : ι) : cut x i = if i ∈ S then 1 else x i := by
    by_cases hi : i ∈ S <;> simp [cut, hi]
  have hc : Continuous cut := continuous_pi fun i ↦ by
    by_cases hi : i ∈ S
    · simpa only [hcut, hi, ite_true] using (continuous_const (y := (1 : M i)) :
        Continuous fun _ : ∀ j, M j ↦ (1 : M i))
    · simpa only [hcut, hi, ite_false] using
        (continuous_apply i : Continuous fun x : ∀ j, M j ↦ x i)
  let f := c.toMonoidHom.comp cut
  have hf : f = 1 := monoidHom_eq_one_of_compact_range_subset_ball f
    (isCompact_range (c.continuous.comp hc)) (by
      rintro _ ⟨x, rfl⟩
      apply hsub
      intro i hi
      change i ∈ S at hi
      rw [hcut, ite_eq_left hi]
      exact mem_of_mem_nhds (hV i))
  refine ⟨S, fun x hx ↦ ?_⟩
  have hfix : cut x = x := by
    funext i
    rw [hcut]
    split_ifs with hi
    · exact (hx i hi).symm
    · rfl
  exact hfix ▸ DFunLike.congr_fun hf x

end RiemannMasullo
