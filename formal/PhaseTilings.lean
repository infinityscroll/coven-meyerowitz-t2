import StripeCollapse

/-!
Actual natural-coefficient convolution and independent phase tilings.
This module does not assume the full Coven--Meyerowitz conjecture.
-/

open scoped BigOperators

noncomputable section

namespace PhaseTilings

open StripeCollapse

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem coefficient_le_convolution (f b : AddMonoidAlgebra ℕ G)
    (x y : G) (hy : b y = 1) : f x ≤ (f * b) (x + y) := by
  by_cases hx : f x = 0
  · simp [hx]
  · rw [AddMonoidAlgebra.mul_apply_left, Finsupp.sum]
    have hmem : x ∈ f.support := Finsupp.mem_support_iff.mpr hx
    have hle := Finset.single_le_sum
      (fun a (_ : a ∈ f.support) => Nat.zero_le (f a * b (-a + (x + y)))) hmem
    simpa [hy] using hle

theorem boolean_of_tiling (f b : AddMonoidAlgebra ℕ G)
    (hb : ∃ y, b y = 1) (htile : f * b = constantMask 1) :
    ∀ x, f x = 0 ∨ f x = 1 := by
  obtain ⟨y, hy⟩ := hb
  intro x
  have hle := coefficient_le_convolution f b x y hy
  rw [htile, constantMask_apply] at hle
  omega

def translate (t : G) (f : AddMonoidAlgebra ℕ G) : AddMonoidAlgebra ℕ G :=
  AddMonoidAlgebra.single t 1 * f

omit [Fintype G] [DecidableEq G] in
@[simp] theorem translate_apply (t x : G) (f : AddMonoidAlgebra ℕ G) :
    translate t f x = f (-t + x) := by
  simp [translate, AddMonoidAlgebra.single_mul_apply]

omit [DecidableEq G] in
@[simp] theorem translate_constant (t : G) :
    translate t (constantMask 1 : AddMonoidAlgebra ℕ G) = constantMask 1 := by
  ext x
  simp

omit [Fintype G] [DecidableEq G] in
@[simp] theorem translate_zero (f : AddMonoidAlgebra ℕ G) :
    translate 0 f = f := by
  ext x
  simp

omit [Fintype G] [DecidableEq G] in
theorem translate_add (t s : G) (f : AddMonoidAlgebra ℕ G) :
    translate (t + s) f = translate t (translate s f) := by
  ext x
  simp [add_assoc, add_comm]

omit [Fintype G] [DecidableEq G] in
theorem invariant_neg (r : G) (f : AddMonoidAlgebra ℕ G)
    (h : translate r f = f) : translate (-r) f = f := by
  have he := congrArg (translate (-r)) h
  rw [← translate_add, neg_add_cancel, translate_zero] at he
  exact he.symm

omit [Fintype G] [DecidableEq G] in
theorem invariant_zsmul (r : G) (f : AddMonoidAlgebra ℕ G)
    (h : translate r f = f) (n : ℤ) : translate (n • r) f = f := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [add_zsmul, one_zsmul, translate_add, h]
    exact ih
  | pred n ih =>
    rw [sub_zsmul, one_zsmul, translate_add, invariant_neg r f h]
    exact ih

omit [Fintype G] [DecidableEq G] in
theorem translate_product (t : G) (f b : AddMonoidAlgebra ℕ G) :
    translate t f * b = translate t (f * b) := by
  exact mul_assoc _ _ _

omit [DecidableEq G] in
theorem phase_sum_tiling {ι : Type*} [Fintype ι]
    (u : ι → AddMonoidAlgebra ℕ G) (b : AddMonoidAlgebra ℕ G)
    (t : ι → G)
    (hinvariant : ∀ i, translate (t i) (u i * b) = u i * b)
    (hpartition : (∑ i, u i * b) = constantMask 1) :
    (∑ i, translate (t i) (u i)) * b = constantMask 1 := by
  rw [Finset.sum_mul]
  simpa only [translate_product, hinvariant] using hpartition

theorem actual_phase_sum {ι : Type*} [Fintype ι]
    (u : ι → AddMonoidAlgebra ℕ G) (b : AddMonoidAlgebra ℕ G)
    (t : ι → G) (hb : ∃ y, b y = 1)
    (hinvariant : ∀ i, translate (t i) (u i * b) = u i * b)
    (hpartition : (∑ i, u i * b) = constantMask 1) :
    ((∑ i, translate (t i) (u i)) * b = constantMask 1) ∧
    (∀ x, (∑ i, translate (t i) (u i)) x = 0 ∨
      (∑ i, translate (t i) (u i)) x = 1) := by
  have ht := phase_sum_tiling u b t hinvariant hpartition
  exact ⟨ht, boolean_of_tiling _ b hb ht⟩

theorem actual_integer_phase_family {ι : Type*} [Fintype ι]
    (u : ι → AddMonoidAlgebra ℕ G) (b : AddMonoidAlgebra ℕ G)
    (r : G) (hb : ∃ y, b y = 1)
    (hperiod : ∀ i, translate r (u i * b) = u i * b)
    (hpartition : (∑ i, u i * b) = constantMask 1) :
    ∀ h : ι → ℤ,
      ((∑ i, translate (h i • r) (u i)) * b = constantMask 1) ∧
      (∀ x, (∑ i, translate (h i • r) (u i)) x = 0 ∨
        (∑ i, translate (h i • r) (u i)) x = 1) := by
  intro h
  exact actual_phase_sum u b (fun i => h i • r) hb
    (fun i => invariant_zsmul r (u i * b) (hperiod i) (h i)) hpartition

end PhaseTilings

#print axioms PhaseTilings.actual_phase_sum
#print axioms PhaseTilings.actual_integer_phase_family
