module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Group.Units

public section

namespace RiemannMasullo

open Topology

/-- A continuous complex character on an open subgroup of an abelian topological group
extends to the full group. Algebraically the complex units are divisible, and continuity
on the open subgroup gives continuity at the identity. -/
theorem exists_complexCharacter_extension_of_isOpenEmbedding {G H : Type*}
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : G →* H) (hi : IsOpenEmbedding i) (c : G →ₜ* ℂ) :
    ∃ C : H →ₜ* ℂ, ∀ g, C (i g) = c g := by
  let : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u ↦ by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz₀ : z ≠ 0 := fun h ↦ u.toMul.ne_zero (by simpa [h, zero_pow hn] using hz.symm)
    exact ⟨Additive.ofMul (Units.mk0 z hz₀), congrArg Additive.ofMul (Units.ext hz)⟩
  let := AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)
  let q := c.toMonoidHom.toHomUnits
  obtain ⟨L, hL⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    i.toAdditive hi.injective q.toAdditive
  let C : H →* ℂˣ := MonoidHom.toAdditive.symm L
  have hC (g : G) : C (i g) = q g := DFunLike.congr_fun hL (Additive.ofMul g)
  have hcont : Continuous C := by
    apply continuous_of_continuousAt_one
    rw [← i.map_one, ← hi.continuousAt_iff]
    rw [show (C ∘ i) = q from funext hC]
    have hq : Continuous q := Units.isEmbedding_val₀.continuous_iff.mpr c.continuous
    exact hq.continuousAt
  exact ⟨⟨(Units.coeHom ℂ).comp C, Units.continuous_val.comp hcont⟩, fun g ↦
    congrArg Units.val (hC g)⟩

end RiemannMasullo
