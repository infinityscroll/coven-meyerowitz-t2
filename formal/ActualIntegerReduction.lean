import ActualPrimeReduction
import T2Induction

/-!
Literal integer-mask interface for the actual prime reduction.
Coefficientwise passage to natural masks is justified by Booleanity.
The final statements contain only actual original tiling/Boolean/base-primary
inputs, not the spectral, stripe, or lower-tiling conclusions.
-/

open scoped BigOperators

noncomputable section

namespace ActualIntegerReduction

open DephasedMasks PeriodicPhaseReduction StripeCollapse T2Induction

def naturalMask {G : Type*} [Fintype G] (A : AddMonoidAlgebra ℤ G) :
    AddMonoidAlgebra ℕ G := Finsupp.equivFunOnFinite.symm (fun x => (A x).toNat)

@[simp] theorem naturalMask_apply {G : Type*} [Fintype G]
    (A : AddMonoidAlgebra ℤ G) (x : G) : naturalMask A x = (A x).toNat := rfl

theorem cast_naturalMask {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : AddMonoidAlgebra ℤ G) (hA : ∀ x, A x = 0 ∨ A x = 1) :
    castMask (naturalMask A) = A := by
  ext x
  rcases hA x with h | h <;> simp [h]

theorem cast_translate {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (t : G) (A : AddMonoidAlgebra ℕ G) :
    castMask (PhaseTilings.translate t A) = AddMonoidAlgebra.single t 1 * castMask A := by
  unfold PhaseTilings.translate
  rw [map_mul]
  congr 1
  ext x
  simp [AddMonoidAlgebra.single_apply]

theorem cast_phase_sum (p M : ℕ) [NeZero p] [NeZero M]
    (A : AddMonoidAlgebra ℕ (ZMod (p * M))) (rho R : ℕ) (h : Fin p → ℤ) :
    castMask (∑ i, PhaseTilings.translate (h i • (R : ZMod M))
      (naturalDephased p M A rho i)) = phaseMask p M (castMask A) rho R h := by
  rw [map_sum]
  unfold phaseMask
  apply Finset.sum_congr rfl
  intro i _
  rw [cast_translate, cast_naturalDephased]
  congr 2
  simp [zsmul_eq_mul, Int.cast_mul, mul_comm]

theorem undo_complement_translation {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (C F : AddMonoidAlgebra ℤ G) (t : G)
    (htile : C * (AddMonoidAlgebra.single t 1 * F) = constantMask 1) :
    C * F = constantMask 1 := by
  have hr : C * (AddMonoidAlgebra.single t 1 * F) =
      AddMonoidAlgebra.single t 1 * (C * F) := by ac_rfl
  rw [hr] at htile
  ext x
  have hx := congrArg (fun D : AddMonoidAlgebra ℤ G => D (t + x)) htile
  simpa [AddMonoidAlgebra.single_mul_apply] using hx

theorem integer_fiber_boolean (p M : ℕ) [NeZero p] [NeZero M]
    (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (hA : ∀ x, A x = 0 ∨ A x = 1) (i : Fin p) :
    ∀ x, integerFiber p M A i x = 0 ∨ integerFiber p M A i x = 1 := by
  intro x
  exact hA _

variable (p a R : ℕ) [NeZero p] [NeZero R]

theorem actual_integer_phase_tilings
    (A B : AddMonoidAlgebra ℤ (ZMod (p * (p ^ a * R))))
    (htile : A * B = constantMask 1) (hp : p.Prime) (hcop : p.Coprime R)
    (hAbool : ∀ x, A x = 0 ∨ A x = 1) (hBbool : ∀ x, B x = 0 ∨ B x = 1)
    (hBprime : Polynomial.cyclotomic p ℤ ∣ CanonicalMaskPolynomial.maskPolynomial B) :
    ∀ h : Fin p → ℤ, ∀ j : Fin p,
      (phaseMask p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) R h *
        dephased p (p ^ a * R) B (PrimeDirectionArithmetic.rho p R) j = constantMask 1) ∧
      (∀ x, phaseMask p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) R h x = 0 ∨
        phaseMask p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) R h x = 1) := by
  have hAn := cast_naturalMask A hAbool
  have hBn := cast_naturalMask B hBbool
  have htileN : naturalMask A * naturalMask B = constantMask (1 : ℕ) := by
    apply castMask_injective
    simpa only [map_mul, hAn, hBn, castMask_constant, Nat.cast_one] using htile
  have hBnBool : ∀ x, naturalMask B x = 0 ∨ naturalMask B x = 1 := by
    intro x
    rcases hBbool x with hx | hx <;> simp [hx]
  have hBnPrime : Polynomial.cyclotomic p ℤ ∣
      CanonicalMaskPolynomial.maskPolynomial (castMask (naturalMask B)) := by
    rwa [hBn]
  intro h j
  obtain ⟨ht, hb⟩ := ActualPrimeReduction.actual_prime_phase_tilings p a R
    (naturalMask A) (naturalMask B) htileN hp hcop hBnBool hBnPrime j h
  constructor
  · simpa only [map_mul, cast_phase_sum, cast_naturalDephased, hAn, hBn,
      castMask_constant, Nat.cast_one] using congrArg castMask ht
  · intro x
    have hc := congrArg (fun C : AddMonoidAlgebra ℤ (ZMod (p ^ a * R)) => C x)
      (cast_phase_sum p (p ^ a * R) (naturalMask A) (PrimeDirectionArithmetic.rho p R) R h)
    rw [hAn] at hc
    dsimp only at hc
    rw [← hc, castMask_apply]
    rcases hb x with hx | hx
    · left
      rw [hx, Nat.cast_zero]
    · right
      rw [hx, Nat.cast_one]

/-- Every actual phase sum also tiles every ordinary original B fiber;
translation of a complement can be undone because the target is J. -/
theorem actual_integer_ordinary_phase_tilings
    (A B : AddMonoidAlgebra ℤ (ZMod (p * (p ^ a * R))))
    (htile : A * B = constantMask 1) (hp : p.Prime) (hcop : p.Coprime R)
    (hAbool : ∀ x, A x = 0 ∨ A x = 1) (hBbool : ∀ x, B x = 0 ∨ B x = 1)
    (hBprime : Polynomial.cyclotomic p ℤ ∣ CanonicalMaskPolynomial.maskPolynomial B) :
    ∀ h : Fin p → ℤ, ∀ j : Fin p,
      (phaseMask p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) R h *
        integerFiber p (p ^ a * R) B j = constantMask 1) ∧
      (∀ x, phaseMask p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) R h x = 0 ∨
        phaseMask p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) R h x = 1) := by
  intro h j
  obtain ⟨ht, hb⟩ := actual_integer_phase_tilings p a R A B htile hp hcop hAbool hBbool hBprime h j
  exact ⟨undo_complement_translation _ _ _ ht, hb⟩

end ActualIntegerReduction

#print axioms ActualIntegerReduction.cast_phase_sum
#print axioms ActualIntegerReduction.undo_complement_translation
#print axioms ActualIntegerReduction.actual_integer_phase_tilings
#print axioms ActualIntegerReduction.actual_integer_ordinary_phase_tilings
