import CyclicT2Completion
import IntegerCyclicReduction

/-!
T2 necessity for genuine integer tilings. The complement is a function on
all of Z and the tiling equation is pointwise exact. Periodicity, collision-
free cyclic reduction, and equality of the ordinary polynomial are derived.
-/

open scoped BigOperators
open Polynomial CanonicalMaskPolynomial T2Induction

noncomputable section

namespace IntegerT2Completion

theorem normalized_integer_tiling_T2 (E : Finset ℕ) (c : ℤ → ℕ)
    (hzero : 0 ∈ E)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    PolynomialT2 (∑ e ∈ E, (X : ℤ[X]) ^ e) := by
  have hE : E.Nonempty := ⟨0, hzero⟩
  obtain ⟨N, hN, hlarge, hperiod, A, B, hA, hB, hAB, hpoly, _, _⟩ :=
    IntegerCyclicReduction.normalized_integer_tiling_to_cyclic E c (E.max' hE)
      hzero (Finset.max'_mem E hE) (fun e he => Finset.le_max' E e he) htile
  letI : NeZero N := ⟨hN.ne'⟩
  rw [← hpoly]
  exact (CyclicT2Completion.actual_cyclic_tiling_T2 A B hA hB hAB).1

theorem cyclotomic_dvd_X_pow_mul_iff (P : ℤ[X]) (k : ℕ) {n : ℕ} (hn : 0 < n) :
    cyclotomic n ℤ ∣ (X : ℤ[X]) ^ k * P ↔ cyclotomic n ℤ ∣ P := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
  rw [T2Induction.cyclotomic_dvd_iff_aeval_zero _ hn hz,
    T2Induction.cyclotomic_dvd_iff_aeval_zero _ hn hz,
    map_mul, map_pow, aeval_X]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero k (hz.ne_zero hn.ne')))

theorem polynomialT2_X_pow_mul (P : ℤ[X]) (k : ℕ) (hP : PolynomialT2 P) :
    PolynomialT2 ((X : ℤ[X]) ^ k * P) := by
  intro S e hS hprime he hprimary
  apply (cyclotomic_dvd_X_pow_mul_iff P k (selectedOrder_pos S e hprime)).mpr
  apply hP S e hS hprime he
  intro q hq
  exact (cyclotomic_dvd_X_pow_mul_iff P k (pow_pos (hprime q hq).pos _)).mp (hprimary q hq)

theorem subtract_min_injective (E : Finset ℕ) (m : ℕ) (hmin : ∀ e ∈ E, m ≤ e) :
    Set.InjOn (fun e : ℕ => e - m) (E : Set ℕ) := by
  intro e he f hf hef
  have hmE := hmin e he
  have hmF := hmin f hf
  change e - m = f - m at hef
  omega

theorem translated_polynomial (E : Finset ℕ) (m : ℕ) (hmin : ∀ e ∈ E, m ≤ e) :
    (∑ e ∈ E, (X : ℤ[X]) ^ e) =
      (X : ℤ[X]) ^ m * ∑ e ∈ E.image (fun e => e - m), (X : ℤ[X]) ^ e := by
  classical
  rw [Finset.sum_image (subtract_min_injective E m hmin), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← pow_add, Nat.add_sub_of_le (hmin e he)]

theorem translated_tiling (E : Finset ℕ) (m : ℕ) (c : ℤ → ℕ)
    (hmin : ∀ e ∈ E, m ≤ e)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    ∀ t : ℤ, (∑ e ∈ E.image (fun e => e - m), c ((t - (e : ℤ)) - (m : ℤ))) = 1 := by
  classical
  intro t
  rw [Finset.sum_image (subtract_min_injective E m hmin)]
  convert htile t using 1
  apply Finset.sum_congr rfl
  intro e he
  rw [Nat.cast_sub (hmin e he)]
  congr 1
  ring

/-- Every actual finite nonnegative integer tile satisfies full T2. There
is no normalization, size, number-of-primes, or period hypothesis. -/
theorem integer_tiling_T2 (E : Finset ℕ) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    PolynomialT2 (∑ e ∈ E, (X : ℤ[X]) ^ e) := by
  classical
  have hE : E.Nonempty := by
    by_contra h
    have hz : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hbad := htile 0
    simp only [hz, Finset.sum_empty] at hbad
    omega
  let m := E.min' hE
  have hmin : ∀ e ∈ E, m ≤ e := fun e he => Finset.min'_le E e he
  have hzero : 0 ∈ E.image (fun e => e - m) := by
    exact Finset.mem_image.mpr ⟨m, Finset.min'_mem E hE, Nat.sub_self m⟩
  have hn := normalized_integer_tiling_T2 (E.image (fun e => e - m))
    (fun t => c (t - (m : ℤ))) hzero (translated_tiling E m c hmin htile)
  rw [translated_polynomial E m hmin]
  exact polynomialT2_X_pow_mul _ m hn

end IntegerT2Completion

#print axioms IntegerT2Completion.normalized_integer_tiling_T2
#print axioms IntegerT2Completion.integer_tiling_T2
