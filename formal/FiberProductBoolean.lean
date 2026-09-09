import CyclicFiberEvaluation
import PhaseTilings

/-!
Each actual ordinary-fiber convolution is a nonnegative partial sum of an
actual convolution on ZMod (p*M), with the literal cyclic carry retained.
The original masks need only have natural coefficients. No Booleanity of
either the original masks or the partial products is assumed.
-/

open scoped BigOperators

noncomputable section

namespace FiberProductBoolean

open CyclicFiberEvaluation StripeCollapse

variable (p M : ℕ) [NeZero p] [NeZero M]

def ordinaryFiber (A : AddMonoidAlgebra ℕ (ZMod (p * M))) (i : Fin p) :
    AddMonoidAlgebra ℕ (ZMod M) :=
  Finsupp.equivFunOnFinite.symm (fun a => A (fiberIndex p M i a))

omit [NeZero p] in
@[simp] theorem ordinaryFiber_apply (A : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (i : Fin p) (a : ZMod M) :
    ordinaryFiber p M A i a = A (fiberIndex p M i a) := rfl

/-- This is an upstairs residue, not a pair in a direct-product group.
In particular the addition of the ordinary digits i,j may carry. -/
def sumIndex (i j : Fin p) (t : ZMod M) : ZMod (p * M) :=
  ((i.val + j.val + p * t.val : ℕ) : ZMod (p * M))

omit [NeZero p] in
theorem fiberIndex_add (i j : Fin p) (a b : ZMod M) :
    fiberIndex p M i a + fiberIndex p M j b = sumIndex p M i j (a + b) := by
  have heq : ((a.val + b.val : ℕ) : ZMod M) = ((a + b).val : ZMod M) := by
    simp
  have hmod : a.val + b.val ≡ (a + b).val [MOD M] :=
    (ZMod.natCast_eq_natCast_iff _ _ M).mp heq
  have hscale : (p : ZMod (p * M)) *
      ((a.val : ZMod (p * M)) + (b.val : ZMod (p * M))) =
      (p : ZMod (p * M)) * ((a + b).val : ZMod (p * M)) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (ZMod.natCast_eq_natCast_iff _ _ (p * M)).mpr (hmod.mul_left' p)
  simp only [fiberIndex, sumIndex, Nat.cast_add, Nat.cast_mul]
  calc
    _ = ((i.val : ZMod (p * M)) + (j.val : ZMod (p * M))) +
      (p : ZMod (p * M)) *
        ((a.val : ZMod (p * M)) + (b.val : ZMod (p * M))) := by ring
    _ = _ := by rw [hscale]

omit [NeZero p] in
theorem complement_index (i j : Fin p) (a t : ZMod M) :
    -fiberIndex p M i a + sumIndex p M i j t =
      fiberIndex p M j (-a + t) := by
  have h : fiberIndex p M i a + fiberIndex p M j (-a + t) =
      sumIndex p M i j t := by
    simpa only [add_neg_cancel_left] using fiberIndex_add p M i j a (-a + t)
  rw [← h]
  simp

theorem natural_mul_apply_fintype {G : Type*} [AddCommGroup G] [Fintype G]
    (A B : AddMonoidAlgebra ℕ G) (x : G) :
    (A * B) x = ∑ a, A a * B (-a + x) := by
  rw [AddMonoidAlgebra.mul_apply_left, Finsupp.sum_fintype]
  intro a
  simp

/-- An explicit inequality at the original carry-correct upstairs output.
The fiber embedding is justified by the proved complete `fiberEquiv`. -/
theorem fiber_product_le_original
    (A B : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (i j : Fin p) (t : ZMod M) :
    (ordinaryFiber p M A i * ordinaryFiber p M B j) t ≤
      (A * B) (sumIndex p M i j t) := by
  have hfull : (A * B) (sumIndex p M i j t) =
      ∑ k : Fin p, ∑ a : ZMod M,
        A (fiberIndex p M k a) *
          B (-fiberIndex p M k a + sumIndex p M i j t) := by
    rw [natural_mul_apply_fintype, ← (fiberEquiv p M).sum_comp
      (fun x => A x * B (-x + sumIndex p M i j t)), Fintype.sum_prod_type]
    rfl
  calc
    (ordinaryFiber p M A i * ordinaryFiber p M B j) t =
        ∑ a : ZMod M, A (fiberIndex p M i a) *
          B (-fiberIndex p M i a + sumIndex p M i j t) := by
      rw [natural_mul_apply_fintype]
      apply Finset.sum_congr rfl
      intro a _
      rw [complement_index]
      rfl
    _ ≤ ∑ k : Fin p, ∑ a : ZMod M,
        A (fiberIndex p M k a) *
          B (-fiberIndex p M k a + sumIndex p M i j t) :=
      Finset.single_le_sum
        (f := fun k => ∑ a : ZMod M, A (fiberIndex p M k a) *
          B (-fiberIndex p M k a + sumIndex p M i j t))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = (A * B) (sumIndex p M i j t) := hfull.symm

theorem ordinary_fiber_product_boolean
    (A B : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (htile : A * B = constantMask 1) :
    ∀ i j : Fin p, ∀ t : ZMod M,
      (ordinaryFiber p M A i * ordinaryFiber p M B j) t = 0 ∨
      (ordinaryFiber p M A i * ordinaryFiber p M B j) t = 1 := by
  intro i j t
  have hle := fiber_product_le_original p M A B i j t
  rw [htile, constantMask_apply] at hle
  omega

theorem translate_boolean {G : Type*} [AddCommGroup G]
    (f : AddMonoidAlgebra ℕ G) (t : G)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    ∀ x, PhaseTilings.translate t f x = 0 ∨ PhaseTilings.translate t f x = 1 := by
  intro x
  simpa only [PhaseTilings.translate_apply] using hf (-t + x)

theorem translated_fiber_product_boolean
    (A B : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (i j : Fin p) (t : ZMod M) :
    ∀ x, PhaseTilings.translate t
        (ordinaryFiber p M A i * ordinaryFiber p M B j) x = 0 ∨
      PhaseTilings.translate t
        (ordinaryFiber p M A i * ordinaryFiber p M B j) x = 1 :=
  translate_boolean _ t (ordinary_fiber_product_boolean p M A B htile i j)

theorem translate_mul_translate {G : Type*} [AddCommGroup G]
    (f g : AddMonoidAlgebra ℕ G) (s t : G) :
    PhaseTilings.translate s f * PhaseTilings.translate t g =
      PhaseTilings.translate (s + t) (f * g) := by
  have h : f * PhaseTilings.translate t g = PhaseTilings.translate t (f * g) := by
    calc
      f * PhaseTilings.translate t g = PhaseTilings.translate t g * f := mul_comm _ _
      _ = PhaseTilings.translate t (g * f) := PhaseTilings.translate_product t g f
      _ = PhaseTilings.translate t (f * g) := congrArg (PhaseTilings.translate t) (mul_comm g f)
  rw [PhaseTilings.translate_product, h, ← PhaseTilings.translate_add]

/-- Arbitrary independent translations of the actual ordinary fibers,
including the manuscript's dephasing, preserve product Booleanity. -/
theorem dephased_fiber_products_boolean
    (A B : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (s t : Fin p → ZMod M) :
    ∀ i j : Fin p, ∀ x : ZMod M,
      (PhaseTilings.translate (s i) (ordinaryFiber p M A i) *
        PhaseTilings.translate (t j) (ordinaryFiber p M B j)) x = 0 ∨
      (PhaseTilings.translate (s i) (ordinaryFiber p M A i) *
        PhaseTilings.translate (t j) (ordinaryFiber p M B j)) x = 1 := by
  intro i j
  simpa only [translate_mul_translate] using
    translated_fiber_product_boolean p M A B htile i j (s i + t j)

#print axioms fiberIndex_add
#print axioms complement_index
#print axioms fiber_product_le_original
#print axioms ordinary_fiber_product_boolean
#print axioms translated_fiber_product_boolean
#print axioms dephased_fiber_products_boolean

end FiberProductBoolean
