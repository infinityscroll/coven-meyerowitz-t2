import IntegerTilingPeriodicity
import CanonicalMaskPolynomial
import Mathlib.Algebra.Ring.Periodic

/-!
Actual normalized integer tiling gives an actual cyclic tiling at a period
larger than the support. The tile polynomial is preserved literally, not
merely at roots of unity. No cyclic tiling or mask identity is assumed.
-/

open scoped BigOperators
open Polynomial StripeCollapse CanonicalMaskPolynomial

noncomputable section

namespace IntegerCyclicReduction

theorem period_above_support (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hzero : 0 ∈ E) (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    ∃ N : ℕ, L < N ∧ Function.Periodic c (N : ℤ) := by
  obtain ⟨P, hP, hperiod⟩ :=
    IntegerTilingPeriodicity.normalized_tiling_periodic E c L hzero hlast hbound htile
  have hlarge : L < (L + 1) * P := by
    have h := Nat.mul_le_mul_left (L + 1) (show 1 ≤ P by omega)
    omega
  refine ⟨(L + 1) * P, hlarge, ?_⟩
  have hp : Function.Periodic c (P : ℤ) := hperiod
  simpa only [Nat.cast_mul] using hp.nat_mul (L + 1)

variable {N : ℕ} [NeZero N]

def tileMask (E : Finset ℕ) : AddMonoidAlgebra ℤ (ZMod N) :=
  ∑ e ∈ E, AddMonoidAlgebra.single (e : ZMod N) 1

def complementMask (c : ℤ → ℕ) : AddMonoidAlgebra ℤ (ZMod N) :=
  Finsupp.equivFunOnFinite.symm (fun x => (c (x.val : ℤ) : ℤ))

@[simp] theorem complementMask_apply (c : ℤ → ℕ) (x : ZMod N) :
    complementMask c x = (c (x.val : ℤ) : ℤ) := rfl

theorem periodic_value_at_representative (c : ℤ → ℕ)
    (hperiod : Function.Periodic c (N : ℤ)) (t : ℤ) :
    c (((t : ZMod N).val : ℕ) : ℤ) = c t := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_iff N t (t : ZMod N)).mp rfl
  have h : c ((((t : ZMod N).val : ℕ) : ℤ) + k * (N : ℤ)) =
      c (((t : ZMod N).val : ℕ) : ℤ) := by
    simpa using (hperiod.int_mul k) (((t : ZMod N).val : ℕ) : ℤ)
  have harg : (((t : ZMod N).val : ℕ) : ℤ) + k * (N : ℤ) = t := by
    calc
      _ = (((t : ZMod N).val : ℕ) : ℤ) + (N : ℤ) * k := by ring
      _ = t := hk.symm
  rw [harg] at h
  exact h.symm

theorem complementMask_intCast (c : ℤ → ℕ)
    (hperiod : Function.Periodic c (N : ℤ)) (t : ℤ) :
    complementMask c (t : ZMod N) = (c t : ℤ) := by
  rw [complementMask_apply, periodic_value_at_representative c hperiod t]

omit [NeZero N] in
theorem tile_residue_no_collision (E : Finset ℕ) (hsmall : ∀ e ∈ E, e < N)
    {e f : ℕ} (he : e ∈ E) (hf : f ∈ E)
    (heq : (e : ZMod N) = (f : ZMod N)) : e = f := by
  have h := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast_of_lt (hsmall e he),
    ZMod.val_natCast_of_lt (hsmall f hf)] using h

theorem tileMask_apply (E : Finset ℕ) (hsmall : ∀ e ∈ E, e < N) (x : ZMod N) :
    tileMask E x = if x.val ∈ E then 1 else 0 := by
  classical
  have heq : ∀ e ∈ E, ((e : ZMod N) = x ↔ e = x.val) := by
    intro e he
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast_of_lt (hsmall e he)] using hv
    · intro h
      rw [h]
      exact ZMod.natCast_zmod_val x
  change (∑ e ∈ E, AddMonoidAlgebra.single (e : ZMod N) (1 : ℤ)) x = _
  simp only [StripeCollapse.sum_apply, Finsupp.single_apply]
  have hsum : (∑ e ∈ E, if (e : ZMod N) = x then (1 : ℤ) else 0) =
      ∑ e ∈ E, if e = x.val then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [heq e he]
  rw [hsum]
  simp

theorem tileMask_boolean (E : Finset ℕ) (hsmall : ∀ e ∈ E, e < N) :
    ∀ x : ZMod N, tileMask E x = 0 ∨ tileMask E x = 1 := by
  intro x
  rw [tileMask_apply E hsmall x]
  split_ifs <;> simp

theorem complementMask_boolean (E : Finset ℕ) (c : ℤ → ℕ) (hzero : 0 ∈ E)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    ∀ x : ZMod N, complementMask c x = 0 ∨ complementMask c x = 1 := by
  intro x
  rcases IntegerTilingPeriodicity.tiling_coefficients_boolean E c hzero htile
    (x.val : ℤ) with h | h
  · exact Or.inl (by simp only [complementMask_apply, h, Nat.cast_zero])
  · exact Or.inr (by simp only [complementMask_apply, h, Nat.cast_one])

theorem cyclic_convolution_of_periodic_tiling (E : Finset ℕ) (c : ℤ → ℕ)
    (hperiod : Function.Periodic c (N : ℤ))
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    tileMask E * complementMask c = (constantMask 1 : AddMonoidAlgebra ℤ (ZMod N)) := by
  ext x
  change (((∑ e ∈ E, AddMonoidAlgebra.single (e : ZMod N) (1 : ℤ)) *
    complementMask c : AddMonoidAlgebra ℤ (ZMod N))) x = 1
  rw [Finset.sum_mul]
  simp only [StripeCollapse.sum_apply, AddMonoidAlgebra.single_mul_apply, one_mul]
  have hs : (∑ e ∈ E, complementMask c (-(e : ZMod N) + x)) =
      ∑ e ∈ E, (c ((x.val : ℤ) - (e : ℤ)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro e he
    have hindex : -(e : ZMod N) + x = (((x.val : ℤ) - (e : ℤ) : ℤ) : ZMod N) := by
      simp [sub_eq_add_neg, add_comm]
    rw [hindex, complementMask_intCast c hperiod]
  rw [hs]
  simpa only [Nat.cast_sum, Nat.cast_one] using
    congrArg (fun n : ℕ => (n : ℤ)) (htile (x.val : ℤ))

theorem maskPolynomial_single_one (x : ZMod N) :
    maskPolynomial (AddMonoidAlgebra.single x (1 : ℤ)) = (X : ℤ[X]) ^ x.val := by
  classical
  simp [maskPolynomial, Finsupp.single_apply]

theorem maskPolynomial_sum {ι : Type*} (s : Finset ι)
    (f : ι → AddMonoidAlgebra ℤ (ZMod N)) :
    maskPolynomial (∑ i ∈ s, f i) = ∑ i ∈ s, maskPolynomial (f i) := by
  simp only [maskPolynomial, StripeCollapse.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem tileMask_polynomial (E : Finset ℕ) (hsmall : ∀ e ∈ E, e < N) :
    maskPolynomial (tileMask (N := N) E) = ∑ e ∈ E, (X : ℤ[X]) ^ e := by
  rw [tileMask, maskPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [maskPolynomial_single_one, ZMod.val_natCast_of_lt (hsmall e he)]

/-! The final bridge has no periodicity or cyclic-mask hypothesis. -/

theorem normalized_integer_tiling_to_cyclic
    (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hzero : 0 ∈ E) (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    ∃ (N : ℕ) (hN : 0 < N),
      letI : NeZero N := ⟨hN.ne'⟩
      L < N ∧ Function.Periodic c (N : ℤ) ∧
      ∃ A B : AddMonoidAlgebra ℤ (ZMod N),
        (∀ x, A x = 0 ∨ A x = 1) ∧
        (∀ x, B x = 0 ∨ B x = 1) ∧
        A * B = constantMask 1 ∧
        maskPolynomial A = ∑ e ∈ E, (X : ℤ[X]) ^ e ∧
        (∀ x, A x = if x.val ∈ E then 1 else 0) ∧
        (∀ t : ℤ, B (t : ZMod N) = (c t : ℤ)) := by
  classical
  obtain ⟨N, hlarge, hperiod⟩ := period_above_support E c L hzero hlast hbound htile
  have hN : 0 < N := by omega
  refine ⟨N, hN, ?_⟩
  letI : NeZero N := ⟨hN.ne'⟩
  have hsmall : ∀ e ∈ E, e < N := fun e he => (hbound e he).trans_lt hlarge
  refine ⟨hlarge, hperiod, tileMask E, complementMask c,
    tileMask_boolean E hsmall, complementMask_boolean E c hzero htile,
    cyclic_convolution_of_periodic_tiling E c hperiod htile,
    tileMask_polynomial E hsmall, ?_, ?_⟩
  · exact tileMask_apply E hsmall
  · exact complementMask_intCast c hperiod

#print axioms period_above_support
#print axioms periodic_value_at_representative
#print axioms tile_residue_no_collision
#print axioms tileMask_boolean
#print axioms complementMask_boolean
#print axioms cyclic_convolution_of_periodic_tiling
#print axioms tileMask_polynomial
#print axioms normalized_integer_tiling_to_cyclic

end IntegerCyclicReduction
