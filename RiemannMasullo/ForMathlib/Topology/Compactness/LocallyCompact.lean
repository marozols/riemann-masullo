module

public import Mathlib.Topology.Compactness.LocallyCompact

public section

open Set Topology

namespace RiemannMasullo

/-- A disjoint union of locally compact spaces is locally compact. -/
instance locallyCompactSpace_sigma {I : Type*} (Y : I → Type*) [∀ i, TopologicalSpace (Y i)]
    [∀ i, LocallyCompactSpace (Y i)] : LocallyCompactSpace (Σ i, Y i) where
  local_compact_nhds := by
    rintro ⟨i, y⟩ U hU
    obtain ⟨K, hKy, hKU, hK⟩ := local_compact_nhds
      ((continuous_sigmaMk (i := i)).continuousAt hU)
    exact ⟨Sigma.mk i '' K, isOpenMap_sigmaMk.image_mem_nhds hKy,
      image_subset_iff.mpr hKU, hK.image continuous_sigmaMk⟩

end RiemannMasullo
