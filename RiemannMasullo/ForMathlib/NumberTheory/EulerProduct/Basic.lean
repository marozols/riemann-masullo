module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum

public section

open Filter Topology

namespace RiemannMasullo

/-- The Euler product for an absolutely summable multiplicative weight. A finite sieve
removes multiples of the selected primes, and its remainder tends to the weight of one. -/
theorem hasProd_eulerFactors_of_summable {M ι : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
    (P : ι → M) (hp : ∀ i, Prime (P i)) (hd : ∀ i j, P i ∣ P j → i = j)
    (hc : ∀ x : M, x ≠ 0 → x ≠ 1 → ∃ i, P i ∣ x) (f : M →*₀ ℂ)
    (hs : Summable fun x ↦ ‖f x‖) (h₁ : ∀ i, f (P i) ≠ 1) :
    HasProd (fun i ↦ (1 - f (P i))⁻¹) (∑' x, f x) := by
  classical
  let good (S : Finset ι) := {x : M | ∀ i ∈ S, ¬ P i ∣ x}
  let w (S : Finset ι) := (good S).indicator (f : M → ℂ)
  let R (S : Finset ι) := ∑' x, w S x
  have hsum (S) : Summable (w S) := (Summable.of_norm (f := fun x : M ↦ f x) hs).indicator _
  have hrec (S : Finset ι) (p : ι) (hpS : p ∉ S) :
      R (insert p S) = (1 - f (P p)) * R S := by
    let d := {x : M | P p ∣ x}.indicator (w S)
    have hdiff (x) : w (insert p S) x = w S x - d x := by
      by_cases h : P p ∣ x
      · have hbad : x ∉ good (insert p S) := fun hx ↦ hx p (Finset.mem_insert_self _ _) h
        simp [w, d, h, hbad]
      · have hiff : x ∈ good (insert p S) ↔ x ∈ good S := by simp [good, h]
        simp only [w, d, Set.indicator_apply, Set.mem_ofPred_eq, h, ite_false, sub_zero, hiff]
    have hcomp (x) : d (P p * x) = f (P p) * w S x := by
      have hiff : P p * x ∈ good S ↔ x ∈ good S := by
        constructor
        · exact fun hx i hi hix ↦ hx i hi (dvd_mul_of_dvd_right hix _)
        · intro hx i hi hdvd
          rcases (hp i).dvd_or_dvd hdvd with hip | hix
          · exact hpS (hd i p hip ▸ hi)
          · exact hx i hi hix
      simp only [d, w, Set.indicator_apply, Set.mem_ofPred_eq, dvd_mul_right, ite_true,
        hiff, map_mul, mul_ite, mul_zero]
    have hdv : Function.support d ⊆ Set.range (fun x ↦ P p * x) := by
      intro x hx
      by_contra hn
      have h : ¬ P p ∣ x := fun ⟨a, ha⟩ ↦ hn ⟨a, ha.symm⟩
      exact hx (by simp [d, h])
    have hinj : Function.Injective (fun x ↦ P p * x) := fun _ _ ↦ mul_left_cancel₀ (hp p).ne_zero
    have hsumd : (∑' x, d x) = f (P p) * R S := by
      rw [← hinj.tsum_eq hdv, tsum_congr hcomp, tsum_mul_left]
    change (∑' x, w (insert p S) x) = _
    rw [tsum_congr hdiff, (hsum S).tsum_sub ((hsum S).indicator _), hsumd]
    change R S - f (P p) * R S = _
    ring
  have hfinite (S : Finset ι) :
      (∏ i ∈ S, (1 - f (P i))⁻¹) * R S = ∑' x, f x := by
    induction S using Finset.induction_on with
    | empty => simp [R, w, good]
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, hrec S i hi, ← ih]
      have hn : 1 - f (P i) ≠ 0 := sub_ne_zero.mpr (h₁ i).symm
      field_simp [hn]
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := w)
      (g := fun x : M ↦ if x = 1 then (1 : ℂ) else 0) hs
    have hx (x : M) : Tendsto (fun S ↦ w S x) atTop (𝓝 (if x = 1 then (1 : ℂ) else 0)) := by
      apply tendsto_const_nhds.congr'
      by_cases h : x = 1
      · subst x
        exact .of_forall fun S ↦ by simp [w, good, fun i ↦ (hp i).not_dvd_one]
      by_cases h0 : x = 0
      · subst x
        exact .of_forall fun S ↦ by simp [w, Set.indicator_apply, h]
      obtain ⟨i, hi⟩ := hc x h0 h
      filter_upwards [Filter.eventually_finset_mem_atTop i] with S hiS
      have hbad : x ∉ good S := fun hs ↦ hs i hiS hi
      simp [w, hbad, h]
    have hb (S : Finset ι) (x : M) : ‖w S x‖ ≤ ‖f x‖ := by
      by_cases hx : x ∈ good S <;> simp [w, hx]
    simpa [R] using h hx (.of_forall hb)
  have hn := hlim.eventually_ne (one_ne_zero : (1 : ℂ) ≠ 0)
  have h := (tendsto_const_nhds (x := ∑' x, f x)).div hlim (by norm_num)
  rw [div_one] at h
  apply h.congr'
  filter_upwards [hn] with S hS
  exact (div_eq_iff hS).mpr (hfinite S).symm

end RiemannMasullo
