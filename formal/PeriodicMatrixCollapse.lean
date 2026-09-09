import PeriodicFactorization
import MatrixCollapse
import FiberMass

/-!
An actual periodic matrix of integral cyclic masks descends to the smaller
cyclic group, collapses there, and lifts to an actual upstairs partition.
The quotient identities and partition are conclusions, not hypotheses.
This file does not derive the matrix hypotheses from a cyclic tiling.
-/

open scoped BigOperators

noncomputable section

namespace PeriodicMatrixCollapse

open PeriodicDescent PeriodicFactorization StripeCollapse

variable (K R : ℕ) [NeZero K] [NeZero R] {p : ℕ} [Fact p.Prime]

/-- The partition masks are Boolean, sum to the literal constant-one mask,
and are periodic on the actual upstairs group. -/
def PeriodicPartition (u : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R))) : Prop :=
  (∀ i x, u i x = 0 ∨ u i x = 1) ∧
  (∑ i, u i) = constantMask 1 ∧
  (∀ i x, u i (x + (R : ZMod (K * R))) = u i x)

omit [Fact p.Prime] in
theorem lift_partition (u : Fin p → AddMonoidAlgebra ℤ (ZMod R))
    (hb : ∀ i x, u i x = 0 ∨ u i x = 1)
    (hs : (∑ i, u i) = constantMask 1) :
    PeriodicPartition K R (fun i => lift K R (u i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i x
    exact hb i (reduction K R x)
  · ext x
    have h := congrArg (fun f : AddMonoidAlgebra ℤ (ZMod R) =>
      f (reduction K R x)) hs
    simpa [lift, pullback] using h
  · intro i x
    exact lift_periodic K R (u i) x

/-- Integral cancellation of the repetition multiplicity precedes the
characteristic-p collapse in `MatrixCollapse`. -/
theorem periodic_matrix_collapse
    (hcop : R.Coprime p)
    (F : Fin p → Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hb : ∀ i j x, F i j x = 0 ∨ F i j x = 1)
    (hr : ∀ i j k l, F i j + F k l = F i l + F k j)
    (ht : (∑ i, ∑ j, F i j) = constantMask (p : ℤ))
    (hm : ∀ i j k l, F i j * F k l = F i l * F k j)
    (hp : ∀ i j x, F i j (x + (R : ZMod (K * R))) = F i j x) :
    (∃ u : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)),
      PeriodicPartition K R u ∧ (∀ i j, F i j = u i)) ∨
    (∃ v : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)),
      PeriodicPartition K R v ∧ (∀ i j, F i j = v j)) := by
  let Q : Fin p → Fin p → AddMonoidAlgebra ℤ (ZMod R) :=
    fun i j => quotientMask K R (F i j)
  have hrep : ∀ i j, lift K R (Q i j) = F i j := by
    intro i j
    exact lift_quotientMask K R (F i j) (hp i j)
  have hqb : ∀ i j x, Q i j x = 0 ∨ Q i j x = 1 := by
    intro i j
    exact quotientMask_boolean K R (F i j) (hb i j)
  have hqr : ∀ i j k l, Q i j + Q k l = Q i l + Q k j := by
    intro i j k l
    simpa only [Q, quotientMask_add] using congrArg (quotientMask K R) (hr i j k l)
  have hqt : (∑ i, ∑ j, Q i j) = constantMask (p : ℤ) := by
    ext x
    have h := congrArg (fun f : AddMonoidAlgebra ℤ (ZMod (K * R)) =>
      f (x.val : ZMod (K * R))) ht
    simpa [Q] using h
  have hqm : ∀ i j k l, Q i j * Q k l = Q i l * Q k j := by
    apply lifted_minors_descend K R Q
    intro i j k l
    simpa only [hrep] using hm i j k l
  have hcard : (Nat.card (ZMod R)).Coprime p := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hcop
  rcases MatrixCollapse.matrix_collapse hcard Q hqb hqr hqt hqm with
    ⟨u, hub, hus, hue⟩ | ⟨v, hvb, hvs, hve⟩
  · left
    refine ⟨fun i => lift K R (u i), lift_partition K R u hub hus, ?_⟩
    intro i j
    exact (hrep i j).symm.trans (congrArg (lift K R) (hue i j))
  · right
    refine ⟨fun j => lift K R (v j), lift_partition K R v hvb hvs, ?_⟩
    intro i j
    exact (hrep i j).symm.trans (congrArg (lift K R) (hve i j))

theorem periodic_matrix_row_collapse
    (hcop : R.Coprime p)
    (F : Fin p → Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hb : ∀ i j x, F i j x = 0 ∨ F i j x = 1)
    (hr : ∀ i j k l, F i j + F k l = F i l + F k j)
    (ht : (∑ i, ∑ j, F i j) = constantMask (p : ℤ))
    (hm : ∀ i j k l, F i j * F k l = F i l * F k j)
    (hp : ∀ i j x, F i j (x + (R : ZMod (K * R))) = F i j x)
    (hvar : ∃ i k j, F i j ≠ F k j) :
    ∃ u : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)),
      PeriodicPartition K R u ∧ (∀ i j, F i j = u i) := by
  rcases periodic_matrix_collapse K R hcop F hb hr ht hm hp with
    h | ⟨v, _, hv⟩
  · exact h
  · obtain ⟨i, k, j, hne⟩ := hvar
    exact False.elim (hne ((hv i j).trans (hv k j).symm))

/-- Product matrices have their convolution minors by commutativity alone;
no rank-one or minor hypothesis is imposed separately. -/
theorem periodic_product_collapse
    (hcop : R.Coprime p)
    (U V : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hb : ∀ i j x, (U i * V j) x = 0 ∨ (U i * V j) x = 1)
    (hr : ∀ i j k l, U i * V j + U k * V l = U i * V l + U k * V j)
    (ht : (∑ i, ∑ j, U i * V j) = constantMask (p : ℤ))
    (hp : ∀ i j x, (U i * V j) (x + (R : ZMod (K * R))) = (U i * V j) x) :
    (∃ u : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)),
      PeriodicPartition K R u ∧ (∀ i j, U i * V j = u i)) ∨
    (∃ v : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)),
      PeriodicPartition K R v ∧ (∀ i j, U i * V j = v j)) := by
  apply periodic_matrix_collapse K R hcop (fun i j => U i * V j) hb hr ht
  · intro i j k l
    ac_rfl
  · exact hp

/-- Unequal actual row-factor masses and one nonzero actual column-factor
mass select the row partition without any quotient-mass hypothesis. -/
theorem periodic_product_row_collapse
    (hcop : R.Coprime p)
    (U V : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)))
    (hb : ∀ i j x, (U i * V j) x = 0 ∨ (U i * V j) x = 1)
    (hr : ∀ i j k l, U i * V j + U k * V l = U i * V l + U k * V j)
    (ht : (∑ i, ∑ j, U i * V j) = constantMask (p : ℤ))
    (hp : ∀ i j x, (U i * V j) (x + (R : ZMod (K * R))) = (U i * V j) x)
    (hU : ∃ i k, FiberMass.mass (U i) ≠ FiberMass.mass (U k))
    (hV : ∃ j, FiberMass.mass (V j) ≠ 0) :
    ∃ u : Fin p → AddMonoidAlgebra ℤ (ZMod (K * R)),
      PeriodicPartition K R u ∧ (∀ i j, U i * V j = u i) := by
  apply periodic_matrix_row_collapse K R hcop (fun i j => U i * V j) hb hr ht
  · intro i j k l
    ac_rfl
  · exact hp
  · obtain ⟨i, k, hik⟩ := hU
    obtain ⟨j, hj⟩ := hV
    exact ⟨i, k, j,
      FiberMass.unequal_masses_force_unequal_products (U i) (U k) (V j) hik hj⟩

#print axioms lift_partition
#print axioms periodic_matrix_collapse
#print axioms periodic_matrix_row_collapse
#print axioms periodic_product_collapse
#print axioms periodic_product_row_collapse

end PeriodicMatrixCollapse
