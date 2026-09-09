import PeriodicDescent

/-!
The converse to coefficient repetition: a mask invariant under translation
by R is the lift of its explicitly chosen canonical-residue coefficients.
No fiber constancy or quotient-existence hypothesis is used.
-/

open scoped BigOperators

noncomputable section

namespace PeriodicFactorization

open PeriodicDescent

variable (K R : ℕ) [NeZero K] [NeZero R]

def quotientMask (f : AddMonoidAlgebra ℤ (ZMod (K * R))) :
    AddMonoidAlgebra ℤ (ZMod R) :=
  Finsupp.equivFunOnFinite.symm (fun y => f (y.val : ZMod (K * R)))

omit [NeZero K] in
@[simp] theorem quotientMask_apply (f : AddMonoidAlgebra ℤ (ZMod (K * R)))
    (y : ZMod R) :
    quotientMask K R f y = f (y.val : ZMod (K * R)) := rfl

omit [NeZero K] in
@[simp] theorem quotientMask_zero : quotientMask K R 0 = 0 := by
  ext y
  rfl

omit [NeZero K] in
@[simp] theorem quotientMask_add (f g : AddMonoidAlgebra ℤ (ZMod (K * R))) :
    quotientMask K R (f + g) = quotientMask K R f + quotientMask K R g := by
  ext y
  rfl

omit [NeZero K] [NeZero R] in
theorem periodic_add_mul (f : AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hf : ∀ x, f (x + (R : ZMod (K * R))) = f x)
    (x : ZMod (K * R)) (n : ℕ) :
    f (x + (n : ZMod (K * R)) * (R : ZMod (K * R))) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa [Nat.cast_succ, add_mul, add_assoc] using
      (hf (x + (n : ZMod (K * R)) * (R : ZMod (K * R)))).trans ih

theorem lift_quotientMask (f : AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hf : ∀ x, f (x + (R : ZMod (K * R))) = f x) :
    lift K R (quotientMask K R f) = f := by
  ext x
  change f ((reduction K R x).val : ZMod (K * R)) = f x
  have hcast : (x.val : ZMod R) = reduction K R x := by
    change (x.val : ZMod R) = ZMod.cast x
    exact ZMod.natCast_val x
  obtain ⟨n, hn⟩ := (ZMod.natCast_eq_iff R x.val (reduction K R x)).mp hcast
  have hx : x = ((reduction K R x).val : ZMod (K * R)) +
      (n : ZMod (K * R)) * (R : ZMod (K * R)) := by
    calc
      x = (x.val : ZMod (K * R)) := (ZMod.natCast_zmod_val x).symm
      _ = _ := by rw [hn]; simp [Nat.cast_add, Nat.cast_mul, mul_comm]
  exact (periodic_add_mul K R f hf
    ((reduction K R x).val : ZMod (K * R)) n).symm.trans (congrArg f hx.symm)

theorem fiber_constancy_of_periodic (f : AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hf : ∀ x, f (x + (R : ZMod (K * R))) = f x)
    {x y : ZMod (K * R)} (hxy : reduction K R x = reduction K R y) :
    f x = f y := by
  have h := lift_quotientMask K R f hf
  calc
    f x = quotientMask K R f (reduction K R x) :=
      (congrArg (fun a : AddMonoidAlgebra ℤ (ZMod (K * R)) => a x) h).symm
    _ = quotientMask K R f (reduction K R y) := congrArg (quotientMask K R f) hxy
    _ = f y := congrArg (fun a : AddMonoidAlgebra ℤ (ZMod (K * R)) => a y) h

@[simp] theorem quotientMask_lift (g : AddMonoidAlgebra ℤ (ZMod R)) :
    quotientMask K R (lift K R g) = g := by
  ext y
  change lift K R g (y.val : ZMod (K * R)) = g y
  simpa only [ZMod.natCast_zmod_val] using lift_apply_nat K R g y.val

theorem exists_unique_lift (f : AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hf : ∀ x, f (x + (R : ZMod (K * R))) = f x) :
    ∃! g : AddMonoidAlgebra ℤ (ZMod R), lift K R g = f := by
  refine ⟨quotientMask K R f, lift_quotientMask K R f hf, ?_⟩
  intro g hg
  exact lift_injective K R (hg.trans (lift_quotientMask K R f hf).symm)

theorem periodic_iff_exists_lift (f : AddMonoidAlgebra ℤ (ZMod (K * R))) :
    (∀ x, f (x + (R : ZMod (K * R))) = f x) ↔
      ∃ g : AddMonoidAlgebra ℤ (ZMod R), lift K R g = f := by
  constructor
  · intro hf
    exact ⟨quotientMask K R f, lift_quotientMask K R f hf⟩
  · rintro ⟨g, rfl⟩
    exact lift_periodic K R g

omit [NeZero K] in
theorem quotientMask_boolean (f : AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    ∀ y, quotientMask K R f y = 0 ∨ quotientMask K R f y = 1 := by
  intro y
  exact hf (y.val : ZMod (K * R))

theorem exists_boolean_lift (f : AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hperiod : ∀ x, f (x + (R : ZMod (K * R))) = f x)
    (hbool : ∀ x, f x = 0 ∨ f x = 1) :
    ∃ g : AddMonoidAlgebra ℤ (ZMod R),
      lift K R g = f ∧ (∀ y, g y = 0 ∨ g y = 1) := by
  exact ⟨quotientMask K R f, lift_quotientMask K R f hperiod,
    quotientMask_boolean K R f hbool⟩

#print axioms lift_quotientMask
#print axioms fiber_constancy_of_periodic
#print axioms quotientMask_lift
#print axioms exists_unique_lift
#print axioms periodic_iff_exists_lift
#print axioms quotientMask_boolean
#print axioms exists_boolean_lift

end PeriodicFactorization
