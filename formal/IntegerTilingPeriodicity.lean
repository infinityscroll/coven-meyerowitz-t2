import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int

/-!
An actual normalized finite integer tiling has a periodic complement.
Both directions of window determinism are derived from the endpoint terms
of the original tiling equation. No recurrence, invertible state machine,
or period is assumed. Natural coefficients become Boolean from that equation.
-/

open scoped BigOperators

namespace IntegerTilingPeriodicity

def WindowEq (c : ℤ → ℕ) (L : ℕ) (s t : ℤ) : Prop :=
  ∀ k : ℕ, k < L → c (s - (k : ℤ)) = c (t - (k : ℤ))

theorem missing_term_eq (E : Finset ℕ) (f g : ℕ → ℕ) (k : ℕ)
    (hk : k ∈ E) (hs : (∑ e ∈ E, f e) = ∑ e ∈ E, g e)
    (heq : ∀ e ∈ E, e ≠ k → f e = g e) : f k = g k := by
  have hrest : (∑ e ∈ E.erase k, f e) = ∑ e ∈ E.erase k, g e := by
    apply Finset.sum_congr rfl
    intro e he
    exact heq e (Finset.mem_erase.mp he).2 (Finset.mem_erase.mp he).1
  have hf := Finset.sum_erase_add E f hk
  have hg := Finset.sum_erase_add E g hk
  rw [hrest] at hf
  exact Nat.add_left_cancel (hf.trans (hs.trans hg.symm))

theorem tiling_coefficients_boolean (E : Finset ℕ) (c : ℤ → ℕ)
    (hzero : 0 ∈ E) (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    ∀ t, c t = 0 ∨ c t = 1 := by
  intro t
  have hle : c t ≤ ∑ e ∈ E, c (t - (e : ℤ)) := by
    simpa only [Nat.cast_zero, sub_zero] using
      (Finset.single_le_sum (f := fun e : ℕ => c (t - (e : ℤ)))
        (fun _ _ => Nat.zero_le _) hzero)
  rw [htile] at hle
  omega

/-- The term at the zero endpoint determines the next value. -/
theorem next_value_eq (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hzero : 0 ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1)
    {s t : ℤ} (hwindow : WindowEq c L s t) : c (s + 1) = c (t + 1) := by
  have h := missing_term_eq E (fun e => c ((s + 1) - (e : ℤ)))
    (fun e => c ((t + 1) - (e : ℤ))) 0 hzero
    ((htile (s + 1)).trans (htile (t + 1)).symm) ?_
  · simpa only [Nat.cast_zero, sub_zero] using h
  · intro e he hne
    change c (s + 1 - (e : ℤ)) = c (t + 1 - (e : ℤ))
    have heL := hbound e he
    have hpred : e - 1 < L := by omega
    have hs : s + 1 - (e : ℤ) = s - ((e - 1 : ℕ) : ℤ) := by omega
    have ht : t + 1 - (e : ℤ) = t - ((e - 1 : ℕ) : ℤ) := by omega
    rw [hs, ht]
    exact hwindow (e - 1) hpred

/-- The term at the maximum endpoint determines the preceding value. -/
theorem previous_value_eq (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1)
    {s t : ℤ} (hwindow : WindowEq c L s t) :
    c (s - (L : ℤ)) = c (t - (L : ℤ)) := by
  apply missing_term_eq E (fun e => c (s - (e : ℤ)))
    (fun e => c (t - (e : ℤ))) L hlast ((htile s).trans (htile t).symm)
  intro e he hne
  exact hwindow e (lt_of_le_of_ne (hbound e he) hne)

theorem window_forward (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hzero : 0 ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1)
    {s t : ℤ} (hwindow : WindowEq c L s t) : WindowEq c L (s + 1) (t + 1) := by
  intro k hk
  by_cases hkzero : k = 0
  · subst k
    simpa only [Nat.cast_zero, sub_zero] using next_value_eq E c L hzero hbound htile hwindow
  · have hpred : k - 1 < L := by omega
    have hs : s + 1 - (k : ℤ) = s - ((k - 1 : ℕ) : ℤ) := by omega
    have ht : t + 1 - (k : ℤ) = t - ((k - 1 : ℕ) : ℤ) := by omega
    rw [hs, ht]
    exact hwindow (k - 1) hpred

theorem window_backward (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1)
    {s t : ℤ} (hwindow : WindowEq c L s t) : WindowEq c L (s - 1) (t - 1) := by
  intro k hk
  have hs : s - 1 - (k : ℤ) = s - ((k + 1 : ℕ) : ℤ) := by omega
  have ht : t - 1 - (k : ℤ) = t - ((k + 1 : ℕ) : ℤ) := by omega
  rw [hs, ht]
  by_cases hlt : k + 1 < L
  · exact hwindow (k + 1) hlt
  · have heq : k + 1 = L := by omega
    rw [heq]
    exact previous_value_eq E c L hlast hbound htile hwindow

/-- Equality of a window propagates in both directions on all of Z. -/
theorem window_all_integer_shifts (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hzero : 0 ∈ E) (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1)
    {s t : ℤ} (hwindow : WindowEq c L s t) :
    ∀ r : ℤ, WindowEq c L (s + r) (t + r) := by
  intro r
  induction r using Int.induction_on with
  | zero => simpa using hwindow
  | succ r ih =>
    simpa only [add_assoc] using window_forward E c L hzero hbound htile ih
  | pred r ih =>
    simpa only [sub_eq_add_neg, add_assoc] using window_backward E c L hlast hbound htile ih

theorem equal_windows_give_period (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hL : 0 < L) (hzero : 0 ∈ E) (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1)
    {s t : ℤ} (hwindow : WindowEq c L s t) :
    ∀ x : ℤ, c (x + (t - s)) = c x := by
  intro x
  have h := window_all_integer_shifts E c L hzero hlast hbound htile hwindow (x - s) 0 hL
  simp only [Nat.cast_zero, sub_zero] at h
  have hs : s + (x - s) = x := by omega
  have ht : t + (x - s) = x + (t - s) := by omega
  rw [hs, ht] at h
  exact h.symm

/-- Actual finite L-bit states, not a hypothesized finite state space. -/
def bitState (c : ℤ → ℕ) (L : ℕ) (hb : ∀ t, c t = 0 ∨ c t = 1)
    (t : ℤ) : Fin L → Fin 2 := fun i =>
  ⟨c (t - (i.val : ℤ)), by rcases hb (t - (i.val : ℤ)) with h | h <;> omega⟩

theorem window_of_state_eq (c : ℤ → ℕ) (L : ℕ)
    (hb : ∀ t, c t = 0 ∨ c t = 1) {s t : ℤ}
    (heq : bitState c L hb s = bitState c L hb t) : WindowEq c L s t := by
  intro k hk
  exact congrArg Fin.val (congrFun heq ⟨k, hk⟩)

theorem positive_length_tiling_periodic (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hL : 0 < L) (hzero : 0 ∈ E) (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : ℤ, c (t + (N : ℤ)) = c t := by
  have hb := tiling_coefficients_boolean E c hzero htile
  have hrepeated : ∃ m n : ℕ, m < n ∧
      bitState c L hb (m : ℤ) = bitState c L hb (n : ℤ) := by
    obtain ⟨m, n, hne, heq⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => bitState c L hb (n : ℤ))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨m, n, hlt, heq⟩
    · exact ⟨n, m, hgt, heq.symm⟩
  obtain ⟨m, n, hmn, heq⟩ := hrepeated
  have hw := window_of_state_eq c L hb heq
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  intro t
  simpa only [Nat.cast_sub hmn.le] using
    equal_windows_give_period E c L hL hzero hlast hbound htile hw t

/-- Full normalized finite-set statement, including L=0. -/
theorem normalized_tiling_periodic (E : Finset ℕ) (c : ℤ → ℕ) (L : ℕ)
    (hzero : 0 ∈ E) (hlast : L ∈ E) (hbound : ∀ e ∈ E, e ≤ L)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : ℤ, c (t + (N : ℤ)) = c t := by
  by_cases hL : L = 0
  · have hE : E = {0} := by
      apply Finset.ext
      intro e
      simp only [Finset.mem_singleton]
      constructor
      · intro he
        have h := hbound e he
        omega
      · intro he
        subst e
        exact hzero
    have hc : ∀ t : ℤ, c t = 1 := by
      intro t
      simpa only [hE, Finset.sum_singleton, Nat.cast_zero, sub_zero] using htile t
    exact ⟨1, Nat.zero_lt_one, fun t => (hc (t + (1 : ℤ))).trans (hc t).symm⟩
  · exact positive_length_tiling_periodic E c L (Nat.pos_of_ne_zero hL)
      hzero hlast hbound htile

#print axioms tiling_coefficients_boolean
#print axioms next_value_eq
#print axioms previous_value_eq
#print axioms window_all_integer_shifts
#print axioms equal_windows_give_period
#print axioms positive_length_tiling_periodic
#print axioms normalized_tiling_periodic

end IntegerTilingPeriodicity
