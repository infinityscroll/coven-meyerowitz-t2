import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NormNum

/-!
Integral convolution of periodic masks, with the repetition multiplicity
proved from actual fibers. This does not formalize the CM carry argument.
-/

open scoped BigOperators

noncomputable section

namespace PeriodicDescent

section FiniteSurjection

variable {E G : Type*} [AddCommGroup E] [AddCommGroup G]
  [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G]

def pullback (π : E →+ G) (f : AddMonoidAlgebra ℤ G) : AddMonoidAlgebra ℤ E :=
  Finsupp.equivFunOnFinite.symm (fun x => f (π x))

omit [Fintype G] [DecidableEq E] [DecidableEq G] in
@[simp] theorem pullback_apply (π : E →+ G) (f : AddMonoidAlgebra ℤ G) (x : E) :
    pullback π f x = f (π x) := rfl

omit [Fintype G] [DecidableEq E] [DecidableEq G] in
theorem pullback_injective (π : E →+ G) (hπ : Function.Surjective π) :
    Function.Injective (pullback π) := by
  intro f g h
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  exact congrArg (fun a : AddMonoidAlgebra ℤ E => a x) h

omit [Fintype G] [DecidableEq E] in
theorem fiber_card_eq (π : E →+ G) (hπ : Function.Surjective π) (y : G) :
    (Finset.univ.filter (fun x => π x = y)).card =
      (Finset.univ.filter (fun x => π x = 0)).card := by
  exact AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)

omit [DecidableEq E] in
theorem sum_pullback (π : E →+ G) (hπ : Function.Surjective π) (h : G → ℤ) :
    (∑ x, h (π x)) =
      ((Finset.univ.filter (fun x => π x = 0)).card : ℤ) * ∑ y, h y := by
  rw [← Finset.sum_fiberwise' Finset.univ π h]
  simp only [Finset.sum_const, fiber_card_eq π hπ, nsmul_eq_mul]
  rw [Finset.mul_sum]

omit [DecidableEq G] in
theorem mul_apply_fintype (f g : AddMonoidAlgebra ℤ G) (x : G) :
    (f * g) x = ∑ y, f y * g (-y + x) := by
  rw [AddMonoidAlgebra.mul_apply_left, Finsupp.sum_fintype]
  intro y
  simp

omit [DecidableEq E] in
theorem pullback_mul (π : E →+ G) (hπ : Function.Surjective π)
    (f g : AddMonoidAlgebra ℤ G) :
    pullback π f * pullback π g =
      (Finset.univ.filter (fun x => π x = 0)).card • pullback π (f * g) := by
  ext x
  rw [mul_apply_fintype]
  simp only [pullback_apply, map_add, map_neg]
  rw [sum_pullback π hπ (fun y => f y * g (-y + π x))]
  change ((Finset.univ.filter (fun x => π x = 0)).card : ℤ) *
    (∑ y, f y * g (-y + π x)) =
    (Finset.univ.filter (fun x => π x = 0)).card • ((f * g) (π x))
  rw [nsmul_eq_mul, mul_apply_fintype]

end FiniteSurjection

section Cyclic

variable (K R : ℕ) [NeZero K] [NeZero R]

def reduction : ZMod (K * R) →+ ZMod R :=
  (ZMod.castHom (Nat.dvd_mul_left R K) (ZMod R)).toAddMonoidHom

omit [NeZero K] [NeZero R] in
theorem reduction_surjective : Function.Surjective (reduction K R) :=
  ZMod.castHom_surjective (Nat.dvd_mul_left R K)

theorem reduction_fiber_card :
    (Finset.univ.filter (fun x => reduction K R x = 0)).card = K := by
  have ht := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (ZMod (K * R))))
    (t := (Finset.univ : Finset (ZMod R)))
    (f := reduction K R) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, fiber_card_eq _ (reduction_surjective K R),
    Finset.sum_const, nsmul_eq_mul, ZMod.card] at ht
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos R) (by simpa [Nat.mul_comm] using ht.symm)

def lift (f : AddMonoidAlgebra ℤ (ZMod R)) : AddMonoidAlgebra ℤ (ZMod (K * R)) :=
  pullback (reduction K R) f

@[simp] theorem lift_zero : lift K R 0 = 0 := by
  ext x
  rfl

@[simp] theorem lift_add (f g : AddMonoidAlgebra ℤ (ZMod R)) :
    lift K R (f + g) = lift K R f + lift K R g := by
  ext x
  rfl

@[simp] theorem lift_apply_nat (f : AddMonoidAlgebra ℤ (ZMod R)) (n : ℕ) :
    lift K R f (n : ZMod (K * R)) = f (n : ZMod R) := by
  simp [lift, reduction, pullback]

theorem lift_periodic (f : AddMonoidAlgebra ℤ (ZMod R)) (x : ZMod (K * R)) :
    lift K R f (x + (R : ZMod (K * R))) = lift K R f x := by
  change f (reduction K R (x + (R : ZMod (K * R)))) = f (reduction K R x)
  simp [reduction]

theorem lift_injective : Function.Injective (lift K R) :=
  pullback_injective _ (reduction_surjective K R)

theorem lift_mul (f g : AddMonoidAlgebra ℤ (ZMod R)) :
    lift K R f * lift K R g = K • lift K R (f * g) := by
  simpa [lift, reduction_fiber_card] using
    pullback_mul (reduction K R) (reduction_surjective K R) f g

theorem convolution_equality_descends (f g h k : AddMonoidAlgebra ℤ (ZMod R))
    (heq : lift K R f * lift K R g = lift K R h * lift K R k) :
    f * g = h * k := by
  rw [lift_mul, lift_mul] at heq
  apply lift_injective K R
  ext x
  have hx := congrArg (fun a : AddMonoidAlgebra ℤ (ZMod (K * R)) => a x) heq
  simpa only [Finsupp.smul_apply, nsmul_eq_mul] using
    (mul_left_cancel₀ (show (K : ℤ) ≠ 0 by exact_mod_cast NeZero.ne K) hx)

theorem lifted_minors_descend {ι : Type*}
    (F : ι → ι → AddMonoidAlgebra ℤ (ZMod R))
    (hminor : ∀ i j k l,
      lift K R (F i j) * lift K R (F k l) =
        lift K R (F i l) * lift K R (F k j)) :
    ∀ i j k l, F i j * F k l = F i l * F k j := by
  intro i j k l
  exact convolution_equality_descends K R _ _ _ _ (hminor i j k l)

#print axioms reduction_fiber_card
#print axioms lift_apply_nat
#print axioms lift_periodic
#print axioms lift_injective
#print axioms lift_mul
#print axioms convolution_equality_descends
#print axioms lifted_minors_descend

end Cyclic

end PeriodicDescent
