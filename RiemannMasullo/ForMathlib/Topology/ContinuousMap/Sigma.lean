module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Topology.ContinuousMap.CompactlySupported

public section

open Function Set Topology
open scoped CompactlySupported DirectSum

namespace RiemannMasullo

/-- A family of maps on a disjoint union is continuous in the compact-open topology
when its restriction to each component varies continuously. -/
theorem continuous_continuousMap_sigma_of_components {A I E : Type*} {Y : I → Type*}
    [TopologicalSpace A] [∀ i, TopologicalSpace (Y i)] [TopologicalSpace E]
    (g : A → C((Σ i, Y i), E)) (h : ∀ i, Continuous (fun a ↦ (g a).comp
      (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, (Σ j, Y j))))) : Continuous g := by
  apply ContinuousMap.continuous_compactOpen.mpr
  intro K hK U hU
  obtain ⟨s, t, hs, ht, rfl⟩ := hK.sigma_exists_finite_sigma_eq
  have heq : {a | MapsTo (g a) (s.sigma t) U} =
      ⋂ i ∈ s, {a | MapsTo (fun y ↦ g a ⟨i, y⟩) (t i) U} := by
    ext a
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun ha i hi y hy ↦ ha ⟨hi, hy⟩, fun ha ⟨i, y⟩ hiy ↦ ha i hiy.1 hiy.2⟩
  rw [heq]
  exact hs.isOpen_biInter fun i _ ↦ (ContinuousMap.isOpen_setOfPred_mapsTo (ht i) hU).preimage (h i)

/-- Restriction to the components of a disjoint union identifies its compactly supported
continuous maps with finitely supported families of compactly supported continuous maps. -/
theorem exists_compactSupport_sigma_linearEquiv (R : Type*) [Semiring R] {I : Type*}
    (Y : I → Type*) [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
    (E : Type*) [AddCommMonoid E] [Module R E] [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousConstSMul R E] :
    ∃ e : C_c((Σ i, Y i), E) ≃ₗ[R] (⨁ i, C_c(Y i, E)), ∀ f i y, e f i y = f ⟨i, y⟩ := by
  classical
  let assemble : (⨁ i, C_c(Y i, E)) →ₗ[R] C_c((Σ i, Y i), E) :=
    { toFun := fun g ↦
        { toFun := fun x ↦ g x.1 x.2
          continuous_toFun := continuous_sigma fun i ↦ (g i).continuous
          hasCompactSupport' := by
            let K := (g.support : Set I).sigma (fun i ↦ tsupport (g i : Y i → E))
            have hK : IsCompact K := Set.isCompact_sigma (Finset.finite_toSet _)
              (fun i _ ↦ (g i).hasCompactSupport)
            apply hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal _ hK.isClosed)
            rintro ⟨i, y⟩ hy
            exact ⟨DFinsupp.mem_support_iff.mpr (fun h ↦ hy (by simp [h])),
              subset_closure hy⟩ }
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hinj : Injective assemble := by
    intro g h he
    exact DFinsupp.ext fun i ↦ DFunLike.ext _ _ fun y ↦
      congrArg (fun f : C_c((Σ i, Y i), E) ↦ f ⟨i, y⟩) he
  have hsurj : Surjective assemble := by
    intro f
    let restrict (i : I) := f.comp (⟨⟨Sigma.mk i, continuous_sigmaMk⟩,
      IsClosedEmbedding.sigmaMk.tendsto_cocompact⟩ : CocompactMap (Y i) (Σ j, Y j))
    obtain ⟨s, t, hs, _, hst⟩ := f.hasCompactSupport.sigma_exists_finite_sigma_eq
    let g : ⨁ i, C_c(Y i, E) := DFinsupp.mk hs.toFinset (fun i ↦ restrict i)
    refine ⟨g, DFunLike.ext _ _ fun ⟨i, y⟩ ↦ ?_⟩
    change g i y = f ⟨i, y⟩
    by_cases hi : i ∈ hs.toFinset
    · rw [show g i = restrict i from DFinsupp.mk_of_mem hi]
      rfl
    · rw [show g i = 0 from DFinsupp.mk_of_notMem hi]
      refine (image_eq_zero_of_notMem_tsupport ?_).symm
      intro hy
      rw [← hst] at hy
      exact hi (hs.mem_toFinset.mpr hy.1)
  let e := LinearEquiv.ofBijective assemble ⟨hinj, hsurj⟩
  exact ⟨e.symm, fun f i y ↦ congrArg (fun g : C_c((Σ i, Y i), E) ↦ g ⟨i, y⟩)
    (e.apply_symm_apply f)⟩

end RiemannMasullo
