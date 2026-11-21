module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import RiemannMasullo.ForMathlib.NumberTheory.EulerProduct.Basic

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

open IsDedekindDomain in
/-- On the half-plane of absolute convergence, the Dedekind zeta function is the Euler
product indexed by the nonzero prime ideals of the ring of integers. -/
theorem dedekindZeta_hasProd (F : Type*) [Field F] [NumberField F] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) ↦ (1 - (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹)
      (dedekindZeta F s) := by
  classical
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs; linarith
  let f : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun I := (I.absNorm : ℂ) ^ (-s)
      map_zero' := by simp [Complex.zero_cpow (neg_ne_zero.mpr hs₀)]
      map_one' := by simp
      map_mul' I J := by
        rw [map_mul, Nat.cast_mul]
        exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg I.absNorm)
          (Nat.cast_nonneg J.absNorm) _ }
  have hnorm (n : ℕ) : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
    obtain rfl | hn := eq_or_ne n 0
    · simp [Complex.zero_cpow (neg_ne_zero.mpr hs₀), Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · exact Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn) _
  have hsum : Summable fun I ↦ ‖f I‖ :=
    (summable_absNorm_rpow F hs).congr fun I ↦ (hnorm I.absNorm).symm
  have hz : (∑' I, f I) = dedekindZeta F s := by
    let e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 F) → ℕ)
    have he : Summable (fun x ↦ f (e x)) := e.summable_iff.mpr hsum.of_norm
    rw [← e.tsum_eq, he.tsum_sigma]
    unfold dedekindZeta LSeries
    refine tsum_congr fun n ↦ ?_
    have (n : ℕ) : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
      (Ring.HasFiniteQuotients.finite_absNorm_eq n).to_subtype
    change (∑' I : {I : Ideal (𝓞 F) // I.absNorm = n}, (I.val.absNorm : ℂ) ^ (-s)) = _
    rw [tsum_congr (fun I : {I : Ideal (𝓞 F) // I.absNorm = n} ↦
      congrArg (fun m : ℕ ↦ (m : ℂ) ^ (-s)) I.property), tsum_const,
      LSeries.term_of_ne_zero' hs₀, Complex.cpow_neg, nsmul_eq_mul, div_eq_mul_inv]
  rw [← hz]
  refine hasProd_eulerFactors_of_summable (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal)
    (fun v ↦ v.prime) ?_ ?_ f hsum ?_
  · intro v w hvw
    exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hvw)).symm
  · intro I hI htop
    obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal (by simpa only [Ideal.one_eq_top] using htop)
    exact ⟨⟨J, hJ.isPrime, fun he ↦ hI (le_bot_iff.mp (he ▸ hIJ))⟩, Ideal.dvd_iff_le.mpr hIJ⟩
  · intro v he
    have hq : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith : -s.re < 0)
    have hval := congrArg norm he
    change ‖(v.asIdeal.absNorm : ℂ) ^ (-s)‖ = ‖(1 : ℂ)‖ at hval
    rw [hnorm, norm_one] at hval
    exact hlt.ne hval

end RiemannMasullo
