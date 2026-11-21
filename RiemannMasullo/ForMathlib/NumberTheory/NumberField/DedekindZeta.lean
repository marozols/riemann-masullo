module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

open NumberField Filter Ideal Set
open scoped Topology

namespace RiemannMasullo

/-- The Dirichlet series defining Dedekind zeta converges absolutely to the right of one. -/
theorem dedekindZeta_LSeriesSummable (F : Type*) [Field F] [NumberField F] {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // I.absNorm = n} : ℂ)) s := by
  -- The nonzero residue gives a point of convergence to the left of any given exponent.
  have hres := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).eventually_ne
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F))
  obtain ⟨t, ht, ht'⟩ := (hres.and (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs))).exists
  apply LSeriesSummable.of_re_le_re (s := (t : ℂ)) ht'.le
  by_contra hdiv
  exact ht (by rw [dedekindZeta, LSeries.eq_zero_of_not_LSeriesSummable _ _ hdiv, mul_zero])

/-- The sum of inverse powers of integral ideal norms converges for each real exponent above one. -/
theorem summable_absNorm_rpow (F : Type*) [Field F] [NumberField F] {r : ℝ} (hr : 1 < r) :
    Summable fun I : Ideal (𝓞 F) ↦ (I.absNorm : ℝ) ^ (-r) := by
  classical
  let A (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 F) // I.absNorm = n}
  have hsum : Summable (fun n : ℕ ↦ A n * (n : ℝ) ^ (-r)) := by
    apply (dedekindZeta_LSeriesSummable F (s := (r : ℂ)) hr).norm.congr
    intro n
    obtain rfl | hn := eq_or_ne n 0
    · simp [Real.zero_rpow (by linarith : -r ≠ 0)]
    · simp [hn, A, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  rw [← (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 F))).summable_iff]
  have (n : ℕ) : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).to_subtype
  refine (summable_sigma_of_nonneg (fun _ ↦ by dsimp; positivity)).2
    ⟨fun _ ↦ Summable.of_finite, hsum.congr fun n ↦ ?_⟩
  change _ = ∑' I : {I : Ideal (𝓞 F) // I.absNorm = n}, (I.val.absNorm : ℝ) ^ (-r)
  rw [tsum_congr (fun I : {I : Ideal (𝓞 F) // I.absNorm = n} ↦
    congrArg (fun m : ℕ ↦ (m : ℝ) ^ (-r)) I.property)]
  simp [A, tsum_const, nsmul_eq_mul]

end RiemannMasullo
