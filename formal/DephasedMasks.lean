import CoprimeTilingFibers
import FiberProductBoolean
import PeriodicPhaseReduction
import SpectralIdentities

/-!
Literal translated ordinary fibers and their character evaluations.
This file supplies the common natural/integer/complex objects used when
assembling the separately checked character cases into mask identities.
-/

open scoped BigOperators

noncomputable section

namespace DephasedMasks

open CyclicFiberEvaluation

variable (p M : ℕ) [NeZero p] [NeZero M]

def integerFiber (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (i : Fin p) :
    AddMonoidAlgebra ℤ (ZMod M) :=
  Finsupp.equivFunOnFinite.symm (fun a => A (fiberIndex p M i a))

omit [NeZero p] in
@[simp] theorem integerFiber_apply (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (i : Fin p) (a : ZMod M) :
    integerFiber p M A i a = A (fiberIndex p M i a) := rfl

def dephased (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (rho : ℕ) (i : Fin p) :
    AddMonoidAlgebra ℤ (ZMod M) :=
  AddMonoidAlgebra.single ((rho * i.val : ℕ) : ZMod M) 1 * integerFiber p M A i

def naturalDephased (A : AddMonoidAlgebra ℕ (ZMod (p * M))) (rho : ℕ) (i : Fin p) :
    AddMonoidAlgebra ℕ (ZMod M) :=
  PhaseTilings.translate ((rho * i.val : ℕ) : ZMod M)
    (FiberProductBoolean.ordinaryFiber p M A i)

theorem cast_integerFiber (A : AddMonoidAlgebra ℕ (ZMod (p * M))) (i : Fin p) :
    PeriodicPhaseReduction.castMask (FiberProductBoolean.ordinaryFiber p M A i) =
      integerFiber p M (PeriodicPhaseReduction.castMask A) i := by
  ext a
  simp

theorem cast_naturalDephased (A : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (rho : ℕ) (i : Fin p) :
    PeriodicPhaseReduction.castMask (naturalDephased p M A rho i) =
      dephased p M (PeriodicPhaseReduction.castMask A) rho i := by
  unfold naturalDephased dephased PhaseTilings.translate
  rw [map_mul, cast_integerFiber]
  congr 1
  ext a
  simp [PeriodicPhaseReduction.castMask_apply, AddMonoidAlgebra.single_apply]

theorem evaluate_single_nat (n : ℕ) {theta : ℂ} (htheta : theta ^ M = 1) :
    CyclicEvaluation.evaluate
      (AddMonoidAlgebra.single (n : ZMod M) 1 : AddMonoidAlgebra ℤ (ZMod M)) theta =
      theta ^ n := by
  simp only [CyclicEvaluation.evaluate, AddMonoidAlgebra.single_apply,
    Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ZMod.val_natCast]
  exact (pow_eq_pow_mod n htheta).symm

omit [NeZero p] in
theorem evaluate_dephased (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (rho : ℕ) (i : Fin p) {theta : ℂ} (htheta : theta ^ M = 1) :
    CyclicEvaluation.evaluate (dephased p M A rho i) theta =
      CoprimeTilingFibers.complexCoefficient p M A theta rho i := by
  rw [dephased, CyclicEvaluation.evaluate_mul _ _ htheta, evaluate_single_nat M _ htheta]
  rfl

theorem natural_products_boolean (A B : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1) (rho : ℕ) :
    ∀ i j x,
      (naturalDephased p M A rho i * naturalDephased p M B rho j) x = 0 ∨
      (naturalDephased p M A rho i * naturalDephased p M B rho j) x = 1 := by
  exact FiberProductBoolean.dephased_fiber_products_boolean p M A B htile
    (fun i => ((rho * i.val : ℕ) : ZMod M))
    (fun j => ((rho * j.val : ℕ) : ZMod M))

theorem integer_products_boolean (A B : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1) (rho : ℕ) :
    ∀ i j x,
      (dephased p M (PeriodicPhaseReduction.castMask A) rho i *
        dephased p M (PeriodicPhaseReduction.castMask B) rho j) x = 0 ∨
      (dephased p M (PeriodicPhaseReduction.castMask A) rho i *
        dephased p M (PeriodicPhaseReduction.castMask B) rho j) x = 1 := by
  intro i j x
  rw [← cast_naturalDephased, ← cast_naturalDephased, ← map_mul,
    PeriodicPhaseReduction.castMask_apply]
  rcases natural_products_boolean p M A B htile rho i j x with h | h <;> simp [h]

end DephasedMasks

#print axioms DephasedMasks.evaluate_dephased
#print axioms DephasedMasks.integer_products_boolean
