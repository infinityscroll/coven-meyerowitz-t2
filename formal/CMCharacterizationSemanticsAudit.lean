import CMCharacterizationSufficiency

/-!
An explicit signed-integer-set semantic interface and exact dependency guards
for the complete characterization. The left side is literal exact covering by
a subset of Z. The right side spells out the normalized mask, the exhaustive
prime-power divisor set, T1, and the distinct-prime T2 quantifiers.

This is a statement-fidelity check of the proved theorem, not an independent
mathematical proof or an external review.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace CMCharacterizationSemanticsAudit

open Classical in
theorem literal_integer_set_characterization (F : Finset ℤ) :
    (∃ C : Set ℤ, ∀ t : ℤ,
      (∑ f ∈ F, if t - f ∈ C then (1 : ℕ) else 0) = 1) ↔
    ∃ hF : F.Nonempty,
      let P : ℤ[X] := ∑ f ∈ F, (X : ℤ[X]) ^ (f - F.min' hF).toNat
      P.eval 1 = ∏ s ∈ (Finset.range (2 * P.natDegree + 1)).filter
        (fun s => (∃ q k : ℕ, q.Prime ∧ 0 < k ∧ s = q ^ k) ∧ cyclotomic s ℤ ∣ P),
          (cyclotomic s ℤ).eval 1
      ∧ ∀ (S : Finset ℕ) (e : ℕ → ℕ), S.Nonempty →
        (∀ q ∈ S, q.Prime) → (∀ q ∈ S, 0 < e q) →
        (∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ P) →
        cyclotomic (∏ q ∈ S, q ^ e q) ℤ ∣ P := by
  rw [← CMCharacterization.tilesZ_iff_boolean_complement,
    CMCharacterization.finite_integer_tiling_iff_T1_T2]
  simp only [CMCharacterization.normalizedMask_eq_literal, CMCharacterization.T1,
    CMCharacterization.primaryDivisors, CMCharacterization.IsPrimary,
    CMCharacterization.T2, T2Induction.PolynomialT2, T2Induction.selectedOrder]

theorem empty_set_not_a_tile : ¬ CMCharacterization.TilesZ ∅ := by
  rintro ⟨c, hc⟩
  have h := hc 0
  simp only [Finset.sum_empty] at h
  omega

theorem every_integer_singleton_tiles (z : ℤ) : CMCharacterization.TilesZ {z} := by
  refine ⟨fun _ => 1, ?_⟩
  intro t
  simp

end CMCharacterizationSemanticsAudit

/-- info: 'CMCharacterization.natural_tiling_of_T1_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.natural_tiling_of_T1_T2

/-- info: 'CMCharacterization.finite_integer_tiling_of_T1_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.finite_integer_tiling_of_T1_T2

/-- info: 'CMCharacterization.finite_integer_tiling_iff_T1_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.finite_integer_tiling_iff_T1_T2

/-- info: 'CMCharacterizationSemanticsAudit.literal_integer_set_characterization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterizationSemanticsAudit.literal_integer_set_characterization
