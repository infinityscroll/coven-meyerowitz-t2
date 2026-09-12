import FullCovenMeyerowitz
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Int

/-!
Classical, period-independent predicates for the Coven--Meyerowitz conditions.
The primary divisor set is a literal finite set of prime powers. Its degree
bound is proved exhaustive for every nonzero polynomial, not assumed from a
chosen cyclic period.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace CMCharacterization

def mask (E : Finset ℕ) : ℤ[X] := ∑ a ∈ E, (X : ℤ[X]) ^ a

def TilesZ (F : Finset ℤ) : Prop :=
  ∃ c : ℤ → ℕ, ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1

def IsPrimary (s : ℕ) : Prop :=
  ∃ q k : ℕ, q.Prime ∧ 0 < k ∧ s = q ^ k

def primaryDivisors (P : ℤ[X]) : Finset ℕ := by
  classical
  exact (Finset.range (2 * P.natDegree + 1)).filter
    (fun s => IsPrimary s ∧ cyclotomic s ℤ ∣ P)

def T1 (P : ℤ[X]) : Prop :=
  P.eval 1 = ∏ s ∈ primaryDivisors P, (cyclotomic s ℤ).eval 1

abbrev T2 (P : ℤ[X]) : Prop := T2Induction.PolynomialT2 P

def normalizedMask (F : Finset ℤ) (hF : F.Nonempty) : ℤ[X] :=
  mask (IntegerSetNormalization.normalizedSet F (F.min' hF))

theorem prime_power_le_twice_totient {q k : ℕ} (hq : q.Prime) (hk : 0 < k) :
    q ^ k ≤ 2 * (q ^ k).totient := by
  cases k with
  | zero => omega
  | succ k =>
    rw [Nat.totient_prime_pow_succ hq, pow_succ]
    have hq' : q ≤ 2 * (q - 1) := by have := hq.two_le; omega
    nlinarith [Nat.mul_le_mul_left (q ^ k) hq']

theorem primary_divisor_degree_bound (P : ℤ[X]) (hP : P ≠ 0)
    {s : ℕ} (hs : IsPrimary s) (hdiv : cyclotomic s ℤ ∣ P) :
    s ≤ 2 * P.natDegree := by
  obtain ⟨q, k, hq, hk, rfl⟩ := hs
  have hd := Polynomial.natDegree_le_of_dvd hdiv hP
  rw [Polynomial.natDegree_cyclotomic] at hd
  exact (prime_power_le_twice_totient hq hk).trans (Nat.mul_le_mul_left 2 hd)

theorem mem_primaryDivisors_iff (P : ℤ[X]) (hP : P ≠ 0) (s : ℕ) :
    s ∈ primaryDivisors P ↔ IsPrimary s ∧ cyclotomic s ℤ ∣ P := by
  classical
  simp only [primaryDivisors, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro hs
    exact ⟨by have := primary_divisor_degree_bound P hP hs.1 hs.2; omega, hs⟩

@[simp] theorem mask_eval_one (E : Finset ℕ) : (mask E).eval 1 = (E.card : ℤ) := by
  simp only [mask, Polynomial.eval_finset_sum, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem mask_ne_zero (E : Finset ℕ) (hE : E.Nonempty) : mask E ≠ 0 := by
  intro h
  have hcard := congrArg (Polynomial.eval (1 : ℤ)) h
  simp only [mask_eval_one, Polynomial.eval_zero, Nat.cast_eq_zero] at hcard
  exact (Finset.card_ne_zero.mpr hE) hcard

end CMCharacterization
