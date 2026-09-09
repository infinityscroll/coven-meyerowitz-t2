import PeriodicMatrixCollapse
import PhaseTilings

/-!
Natural-to-integer integration of periodic product collapse with actual
independent-phase tilings. The row partition and smaller-group tiling
identity are derived, not assumed. This does not derive the product
hypotheses or unequal fiber masses from the original cyclic carry equation.
-/

open scoped BigOperators

noncomputable section

namespace PeriodicPhaseReduction

open StripeCollapse

section Cast

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Coefficientwise casting of an actual natural mask to an integer mask. -/
def castMask : AddMonoidAlgebra ℕ G →+* AddMonoidAlgebra ℤ G :=
  AddMonoidAlgebra.mapRangeRingHom G (Nat.castRingHom ℤ)

@[simp] theorem castMask_apply (f : AddMonoidAlgebra ℕ G) (x : G) :
    castMask f x = (f x : ℤ) := by
  simp [castMask, AddMonoidAlgebra.mapRangeRingHom_apply]

theorem castMask_injective : Function.Injective (castMask (G := G)) := by
  intro f g h
  ext x
  have hx := congrArg (fun a : AddMonoidAlgebra ℤ G => a x) h
  simpa only [castMask_apply, Nat.cast_inj] using hx

@[simp] theorem castMask_constant (n : ℕ) :
    castMask (constantMask n : AddMonoidAlgebra ℕ G) = constantMask (n : ℤ) := by
  ext x
  simp

end Cast

variable (K R : ℕ) [NeZero K] [NeZero R] {p : ℕ} [Fact p.Prime]

/-- For any chosen actual nonempty Boolean V_j, the matrix hypotheses imply
that every independently R-shifted sum of U_i is Boolean and tiles V_j. -/
theorem periodic_product_phase_tilings
    (hcop : R.Coprime p)
    (U V : Fin p → AddMonoidAlgebra ℕ (ZMod (K * R)))
    (hb : ∀ i j x, (U i * V j) x = 0 ∨ (U i * V j) x = 1)
    (hr : ∀ i j k l, U i * V j + U k * V l = U i * V l + U k * V j)
    (ht : (∑ i, ∑ j, U i * V j) = constantMask (p : ℕ))
    (hp : ∀ i j x, (U i * V j) (x + (R : ZMod (K * R))) = (U i * V j) x)
    (hU : ∃ i k, FiberMass.mass (castMask (U i)) ≠ FiberMass.mass (castMask (U k)))
    (j : Fin p)
    (hVbool : ∀ x, V j x = 0 ∨ V j x = 1)
    (hVnonempty : ∃ x, V j x = 1) :
    ∀ h : Fin p → ℤ,
      ((∑ i, PhaseTilings.translate (h i • (R : ZMod (K * R))) (U i)) * V j =
        constantMask 1) ∧
      (∀ x, (∑ i, PhaseTilings.translate (h i • (R : ZMod (K * R))) (U i)) x = 0 ∨
        (∑ i, PhaseTilings.translate (h i • (R : ZMod (K * R))) (U i)) x = 1) := by
  have hbi : ∀ i j x,
      (castMask (U i) * castMask (V j)) x = 0 ∨
      (castMask (U i) * castMask (V j)) x = 1 := by
    intro i j x
    rcases hb i j x with h | h
    · left
      simp only [← map_mul, castMask_apply, h, Nat.cast_zero]
    · right
      simp only [← map_mul, castMask_apply, h, Nat.cast_one]
  have hri : ∀ i j k l,
      castMask (U i) * castMask (V j) + castMask (U k) * castMask (V l) =
      castMask (U i) * castMask (V l) + castMask (U k) * castMask (V j) := by
    intro i j k l
    simpa only [map_add, map_mul] using congrArg castMask (hr i j k l)
  have hti : (∑ i, ∑ j, castMask (U i) * castMask (V j)) =
      constantMask (p : ℤ) := by
    simpa only [map_sum, map_mul, castMask_constant] using congrArg castMask ht
  have hpi : ∀ i j x,
      (castMask (U i) * castMask (V j)) (x + (R : ZMod (K * R))) =
      (castMask (U i) * castMask (V j)) x := by
    intro i j x
    simpa only [← map_mul, castMask_apply] using
      congrArg (fun n : ℕ => (n : ℤ)) (hp i j x)
  have hVbi : ∀ x, castMask (V j) x = 0 ∨ castMask (V j) x = 1 := by
    intro x
    rcases hVbool x with h | h <;> simp [h]
  have hVni : ∃ x, castMask (V j) x = 1 := by
    obtain ⟨x, hx⟩ := hVnonempty
    exact ⟨x, by simp [hx]⟩
  have hVm : FiberMass.mass (castMask (V j)) ≠ 0 :=
    ne_of_gt (FiberMass.mass_pos_of_boolean_nonempty _ hVbi hVni)
  obtain ⟨A, hA, hprod⟩ :=
    PeriodicMatrixCollapse.periodic_product_row_collapse K R hcop
      (fun i => castMask (U i)) (fun j => castMask (V j))
      hbi hri hti hpi hU ⟨j, hVm⟩
  have hpartition : (∑ i, U i * V j) = constantMask 1 := by
    apply castMask_injective
    calc
      castMask (∑ i, U i * V j) = ∑ i, castMask (U i) * castMask (V j) := by simp
      _ = ∑ i, A i := by simp_rw [hprod]
      _ = constantMask 1 := hA.2.1
      _ = castMask (constantMask 1) := by simp
  have hperiod : ∀ i,
      PhaseTilings.translate (R : ZMod (K * R)) (U i * V j) = U i * V j := by
    intro i
    ext x
    rw [PhaseTilings.translate_apply]
    simpa [add_assoc, add_comm, add_left_comm] using
      (hp i j (-(R : ZMod (K * R)) + x)).symm
  exact PhaseTilings.actual_integer_phase_family U (V j) (R : ZMod (K * R))
    hVnonempty hperiod hpartition

#print axioms castMask_injective
#print axioms periodic_product_phase_tilings

end PeriodicPhaseReduction
