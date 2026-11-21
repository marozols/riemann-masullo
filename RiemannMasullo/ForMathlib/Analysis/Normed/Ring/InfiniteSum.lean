module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-! # Products of nonnegative series over finitely many independent indices -/

@[expose] public section

namespace RiemannMasullo

/-- Sums of products over a finite tuple of independent indices factor when each
coordinate series is nonnegative and summable. -/
theorem hasSum_prod_fin_of_nonneg {m : ℕ} {ι : Fin m → Type*}
    (f : (i : Fin m) → ι i → ℝ) (s : Fin m → ℝ)
    (hf : ∀ i j, 0 ≤ f i j) (hs : ∀ i, HasSum (f i) (s i)) :
    HasSum (fun k : (i : Fin m) → ι i ↦ ∏ i, f i (k i)) (∏ i, s i) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    let tail (k : (i : Fin m) → ι i.succ) := ∏ i, f i.succ (k i)
    have ht : HasSum tail (∏ i : Fin m, s i.succ) :=
      ih (fun i ↦ f i.succ) (fun i ↦ s i.succ) (fun i ↦ hf i.succ) (fun i ↦ hs i.succ)
    have hp := (hs 0).mul ht ((hs 0).summable.mul_of_nonneg ht.summable
      (hf 0) (fun k ↦ Finset.prod_nonneg fun i _ ↦ hf _ _))
    apply (Fin.consEquiv ι).hasSum_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv, tail] using hp

end RiemannMasullo
