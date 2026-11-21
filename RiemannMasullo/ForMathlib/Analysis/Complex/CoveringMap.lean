module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

namespace RiemannMasullo
open Function Set Topology

/-- Exponentiating with base greater than one identifies the period cylinder with the
nonzero complex numbers, also after multiplication by a fixed unit. -/
theorem exists_complexPowerCylinder (q : ℝ) (hq : 1 < q) (b : ℂˣ) :
    let P := AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I / (Real.log q : ℂ))
    ∃ e : (ℂ ⧸ P) ≃ₜ ℂˣ, ∀ s : ℂ, (e (QuotientAddGroup.mk s) : ℂ) = b * (q : ℂ) ^ (-s) := by
  let L : ℂ := Real.log q
  have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  let T : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let P := AddSubgroup.zmultiples (T / L)
  let expNonzero (z : ℂ) : {w : ℂ // w ≠ 0} := ⟨Complex.exp z, z.exp_ne_zero⟩
  let expUnit : ℂ → ℂˣ := (unitsHomeomorphNeZero (G₀ := ℂ)).symm ∘ expNonzero
  have hval (z : ℂ) : (expUnit z : ℂ) = Complex.exp z :=
    congrArg Subtype.val ((unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply (expNonzero z))
  let f (s : ℂ) : ℂˣ := b * expUnit (-L * s)
  have hexp : IsOpenQuotientMap expUnit := by
    apply (unitsHomeomorphNeZero (G₀ := ℂ)).symm.isOpenQuotientMap.comp (f := expNonzero)
    exact ⟨fun z ↦ ⟨Complex.log z, Subtype.ext (Complex.exp_log z.prop)⟩,
      Complex.isCoveringMap_exp.continuous, Complex.isCoveringMap_exp.isOpenMap⟩
  have hf : IsOpenQuotientMap f := (Homeomorph.mulLeft b).isOpenQuotientMap.comp
    (hexp.comp (Homeomorph.mulLeft₀ (-L) (neg_ne_zero.mpr hL)).isOpenQuotientMap)
  have hfiber (x y : ℂ) :
      f x = f y ↔ (QuotientAddGroup.mk x : ℂ ⧸ P) = QuotientAddGroup.mk y := by
    change b * expUnit (-L * x) = b * expUnit (-L * y) ↔ _
    rw [mul_left_cancel_iff, ← Units.val_inj, QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
    rw [hval, hval]
    change Complex.exp (-L * x) = Complex.exp (-L * y) ↔ ∃ k : ℤ, k • (T / L) = -x + y
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine exists_congr fun k ↦ ?_
    rw [zsmul_eq_mul, mul_div_assoc', div_eq_iff hL]
    change -L * x = -L * y + (k : ℂ) * T ↔ _
    constructor <;> intro h <;> linear_combination -h
  let g : (ℂ ⧸ P) → ℂˣ := Quotient.lift f (fun x y h ↦ (hfiber x y).mpr (Quotient.sound h))
  have hg : IsOpenQuotientMap g := (IsOpenQuotientMap.of_comp_iff
    (g := g) QuotientAddGroup.isOpenQuotientMap_mk).mp hf
  have hinj : Injective g := by
    intro x y
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact (hfiber u v).mp
  let e := (Equiv.ofBijective g ⟨hinj, hg.surjective⟩).toHomeomorphOfContinuousOpen
    hg.continuous hg.isOpenMap
  refine ⟨e, fun s ↦ ?_⟩
  change (b : ℂ) * (expUnit (-L * s) : ℂ) = _
  rw [hval]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hq).ne'),
    ← Complex.ofReal_log (zero_lt_one.trans hq).le, mul_neg, neg_mul]

end RiemannMasullo
