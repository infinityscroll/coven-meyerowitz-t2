import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int

/-!
Mass of an actual integral group-algebra mask and exclusion of a column-only
product pattern. Multiplication is convolution; no Boolean hypotheses are
needed for multiplicativity or cancellation of a nonzero integer mass.
This file does not establish the original tiling's unequal fiber masses.
-/

open scoped BigOperators

noncomputable section

namespace FiberMass

variable {G : Type*} [AddCommGroup G] [Fintype G]

def mass (f : AddMonoidAlgebra ℤ G) : ℤ := ∑ x, f x

/-- The augmentation homomorphism sends every group basis element to 1. -/
def massHom : AddMonoidAlgebra ℤ G →+* ℤ :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id ℤ)
    (1 : Multiplicative G →* ℤ) (fun _ _ => by simp [Commute])

theorem massHom_apply (f : AddMonoidAlgebra ℤ G) : massHom f = mass f := by
  change f.sum (fun _ b => b * 1) = ∑ x, f x
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp

/-- The actual sum of coefficients is multiplicative for convolution. -/
theorem mass_mul (f g : AddMonoidAlgebra ℤ G) :
    mass (f * g) = mass f * mass g := by
  simpa only [massHom_apply] using (massHom (G := G)).map_mul f g

theorem equal_products_force_equal_masses (u u' v : AddMonoidAlgebra ℤ G)
    (hv : mass v ≠ 0) (h : u * v = u' * v) : mass u = mass u' := by
  have hm := congrArg mass h
  simp only [mass_mul] at hm
  exact mul_right_cancel₀ hv hm

theorem unequal_masses_force_unequal_products (u u' v : AddMonoidAlgebra ℤ G)
    (hu : mass u ≠ mass u') (hv : mass v ≠ 0) : u * v ≠ u' * v := by
  intro h
  exact hu (equal_products_force_equal_masses u u' v hv h)

/-- At any fixed column with nonzero mass, equal products force all row
factor masses to be equal. No finiteness of the index families is needed. -/
theorem column_constant_forces_equal_masses {ι κ : Type*}
    (u : ι → AddMonoidAlgebra ℤ G) (v : κ → AddMonoidAlgebra ℤ G)
    (j : κ) (hv : mass (v j) ≠ 0)
    (hcolumn : ∀ i k, u i * v j = u k * v j) :
    ∀ i k, mass (u i) = mass (u k) := by
  intro i k
  exact equal_products_force_equal_masses (u i) (u k) (v j) hv (hcolumn i k)

/-- Unequal row-factor masses and one nonzero column-factor mass rule out
the column-only orientation, in which products do not depend on row index. -/
theorem unequal_masses_exclude_column_only {ι κ : Type*}
    (u : ι → AddMonoidAlgebra ℤ G) (v : κ → AddMonoidAlgebra ℤ G)
    (hu : ∃ i k, mass (u i) ≠ mass (u k))
    (hv : ∃ j, mass (v j) ≠ 0) :
    ¬ (∀ i k j, u i * v j = u k * v j) := by
  obtain ⟨i, k, hik⟩ := hu
  obtain ⟨j, hj⟩ := hv
  intro hcolumn
  exact unequal_masses_force_unequal_products (u i) (u k) (v j) hik hj
    (hcolumn i k j)

/-- A Boolean mask containing an actual point has strictly positive mass. -/
theorem mass_pos_of_boolean_nonempty (v : AddMonoidAlgebra ℤ G)
    (hv : ∀ x, v x = 0 ∨ v x = 1) (hne : ∃ x, v x = 1) :
    0 < mass v := by
  apply Finset.sum_pos'
  · intro x hx
    rcases hv x with h | h <;> simp [h]
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, Finset.mem_univ x, by simp [hx]⟩

#print axioms mass_mul
#print axioms unequal_masses_exclude_column_only
#print axioms mass_pos_of_boolean_nonempty

end FiberMass
