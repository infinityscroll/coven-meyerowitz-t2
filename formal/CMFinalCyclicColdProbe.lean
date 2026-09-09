import CyclicT2Completion

/- Fresh audit probe. This file was authored without relying on prior verdicts.
Its conclusion and hypotheses expose functions, cyclic convolution, and ordinary
integer polynomials directly; no project target predicate occurs in its type. -/

open scoped BigOperators
open Polynomial
noncomputable section

namespace CMFinalCyclicColdProbe

theorem literal_function_cyclic_T2 (N : ℕ) [NeZero N]
    (f g : ZMod N → ℤ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hg : ∀ x, g x = 0 ∨ g x = 1)
    (hconvolution : ∀ t, (∑ x : ZMod N, f x * g (t - x)) = 1) :
    (∀ (S : Finset ℕ) (e : ℕ → ℕ), S.Nonempty →
      (∀ q ∈ S, Nat.Prime q) → (∀ q ∈ S, 0 < e q) →
      (∀ q ∈ S, Polynomial.cyclotomic (q ^ e q) ℤ ∣
        ∑ x : ZMod N, Polynomial.C (f x) * Polynomial.X ^ x.val) →
      Polynomial.cyclotomic (∏ q ∈ S, q ^ e q) ℤ ∣
        ∑ x : ZMod N, Polynomial.C (f x) * Polynomial.X ^ x.val) ∧
    (∀ (S : Finset ℕ) (e : ℕ → ℕ), S.Nonempty →
      (∀ q ∈ S, Nat.Prime q) → (∀ q ∈ S, 0 < e q) →
      (∀ q ∈ S, Polynomial.cyclotomic (q ^ e q) ℤ ∣
        ∑ x : ZMod N, Polynomial.C (g x) * Polynomial.X ^ x.val) →
      Polynomial.cyclotomic (∏ q ∈ S, q ^ e q) ℤ ∣
        ∑ x : ZMod N, Polynomial.C (g x) * Polynomial.X ^ x.val) := by
  let A : AddMonoidAlgebra ℤ (ZMod N) := Finsupp.equivFunOnFinite.symm f
  let B : AddMonoidAlgebra ℤ (ZMod N) := Finsupp.equivFunOnFinite.symm g
  have htile : A * B = StripeCollapse.constantMask 1 := by
    ext t
    rw [PeriodicDescent.mul_apply_fintype]
    change (∑ x : ZMod N, f x * g (-x + t)) = 1
    simpa only [sub_eq_add_neg, add_comm] using hconvolution t
  exact CyclicT2Completion.actual_cyclic_tiling_T2 A B hf hg htile

theorem positive_period_instance (N : ℕ) (hN : 0 < N) : Nonempty (NeZero N) :=
  ⟨⟨hN.ne'⟩⟩

theorem nonvacuous_tiling_every_period (N : ℕ) [NeZero N] :
    ∃ A B : AddMonoidAlgebra ℤ (ZMod N),
      (∀ x, A x = 0 ∨ A x = 1) ∧
      (∀ x, B x = 0 ∨ B x = 1) ∧
      A * B = StripeCollapse.constantMask 1 := by
  refine ⟨AddMonoidAlgebra.single 0 1, StripeCollapse.constantMask 1, ?_, ?_, ?_⟩
  · intro x
    classical
    by_cases hx : 0 = x <;> simp [hx]
  · intro x
    exact Or.inr rfl
  · ext x
    simp [AddMonoidAlgebra.single_mul_apply]

#check @CyclicT2Completion.actual_cyclic_tiling_T2
#print axioms literal_function_cyclic_T2
#print axioms nonvacuous_tiling_every_period
#print axioms CyclicT2Completion.actual_cyclic_tiling_T2
#print axioms ActualIntegerReduction.actual_integer_ordinary_phase_tilings
#print axioms ActualPrimeReduction.actual_prime_phase_tilings
#print axioms PrimaryAllocation.primary_divisor_within_period_pos
#print axioms CommonComplementLift.prime_power_inherits

end CMFinalCyclicColdProbe
