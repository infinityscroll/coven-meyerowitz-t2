import BooleanStripes

/-!
Combines the constructed Boolean stripe partition with the proved
characteristic-p collapse. The input is an actual matrix of integer
group-algebra elements, not a preassigned stripe partition.
This is not the carry/Fourier argument or the full CM theorem.
-/

open scoped BigOperators

noncomputable section

namespace MatrixCollapse

open StripeCollapse

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {p : ℕ} [Fact p.Prime]

theorem matrix_collapse
    (hcop : (Nat.card G).Coprime p)
    (F : Fin p → Fin p → AddMonoidAlgebra ℤ G)
    (hb : ∀ i j x, F i j x = 0 ∨ F i j x = 1)
    (hr : ∀ i j k l, F i j + F k l = F i l + F k j)
    (ht : (∑ i, ∑ j, F i j) = constantMask (p : ℤ))
    (hm : ∀ i j k l, F i j * F k l = F i l * F k j) :
    (∃ u : Fin p → AddMonoidAlgebra ℤ G,
      (∀ i x, u i x = 0 ∨ u i x = 1) ∧
      (∑ i, u i) = constantMask 1 ∧ (∀ i j, F i j = u i)) ∨
    (∃ v : Fin p → AddMonoidAlgebra ℤ G,
      (∀ j x, v j x = 0 ∨ v j x = 1) ∧
      (∑ j, v j) = constantMask 1 ∧ (∀ i j, F i j = v j)) := by
  obtain ⟨u, v, hu, hv, hp, hf, _⟩ :=
    BooleanStripes.groupAlgebra_stripe_decomposition (Fact.out : p.Prime).two_le
      F hb hr ht
  have hminor : ∀ i j k l, (u i + v j) * (u k + v l) =
      (u i + v l) * (u k + v j) := by
    intro i j k l
    simpa only [hf] using hm i j k l
  rcases stripe_collapse_integral p hcop u v hu hv hp hminor with hz | hz
  · right
    refine ⟨v, hv, ?_, ?_⟩
    · simpa [hz] using hp
    · intro i j
      simpa [hz] using hf i j
  · left
    refine ⟨u, hu, ?_, ?_⟩
    · simpa [hz] using hp
    · intro i j
      simpa [hz] using hf i j

theorem matrix_row_collapse
    (hcop : (Nat.card G).Coprime p)
    (F : Fin p → Fin p → AddMonoidAlgebra ℤ G)
    (hb : ∀ i j x, F i j x = 0 ∨ F i j x = 1)
    (hr : ∀ i j k l, F i j + F k l = F i l + F k j)
    (ht : (∑ i, ∑ j, F i j) = constantMask (p : ℤ))
    (hm : ∀ i j k l, F i j * F k l = F i l * F k j)
    (hvar : ∃ i k j, F i j ≠ F k j) :
    ∃ u : Fin p → AddMonoidAlgebra ℤ G,
      (∀ i x, u i x = 0 ∨ u i x = 1) ∧
      (∑ i, u i) = constantMask 1 ∧ (∀ i j, F i j = u i) := by
  rcases matrix_collapse hcop F hb hr ht hm with h | ⟨v, _, _, hv⟩
  · exact h
  · obtain ⟨i, k, j, hne⟩ := hvar
    exact False.elim (hne ((hv i j).trans (hv k j).symm))

end MatrixCollapse

#print axioms MatrixCollapse.matrix_collapse
#print axioms MatrixCollapse.matrix_row_collapse
