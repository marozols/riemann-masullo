module

public import Mathlib.Analysis.InnerProductSpace.Subspace

/-! # Summability of orthogonal families -/

public section

open scoped InnerProductSpace

namespace RiemannMasullo

/-- A pairwise orthogonal family of vectors in a Hilbert space is summable
if and only if its squared norms are summable. -/
theorem summable_iff_summable_sq_norm_of_orthogonal {𝕜 ι E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) :
    Summable v ↔ Summable fun i ↦ ‖v i‖ ^ 2 := by
  let S (i : ι) := Submodule.span 𝕜 {v i}
  have hS : OrthogonalFamily 𝕜 (fun i ↦ S i) (fun i ↦ (S i).subtypeₗᵢ) := by
    intro i j hij u w
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp u.property
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp w.property
    change ⟪(u : E), (w : E)⟫_𝕜 = 0
    rw [← ha, ← hb, inner_smul_left, inner_smul_right, hv hij, mul_zero, mul_zero]
  exact hS.summable_iff_norm_sq_summable fun i ↦
    (⟨v i, Submodule.mem_span_singleton_self _⟩ : S i)

end RiemannMasullo
