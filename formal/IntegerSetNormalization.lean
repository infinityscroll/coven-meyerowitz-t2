import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int

/-!
Normalize an actual finite integer tiling by its derived minimum. The natural
image, the translation bijection, and the shifted complement tiling equation
are all constructed. No nonemptiness, normalization, period, or T2 property
is assumed.
-/

open scoped BigOperators

namespace IntegerSetNormalization

def normalizedSet (F : Finset ℤ) (m : ℤ) : Finset ℕ :=
  F.image (fun f => (f - m).toNat)

def shiftedComplement (c : ℤ → ℕ) (m : ℤ) : ℤ → ℕ :=
  fun t => c (t - m)

theorem tiling_set_nonempty (F : Finset ℤ) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) : F.Nonempty := by
  by_contra h
  have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have ht := htile 0
  simp only [hF, Finset.sum_empty] at ht
  omega

theorem translate_normalized_index (m f : ℤ) (h : m ≤ f) :
    m + ((f - m).toNat : ℤ) = f := by
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr h)]
  omega

theorem normalized_index_translate (m : ℤ) (e : ℕ) :
    ((m + (e : ℤ)) - m).toNat = e := by
  simp

theorem normalized_index_injective_on (F : Finset ℤ) (m : ℤ)
    (hmin : ∀ f ∈ F, m ≤ f) :
    Set.InjOn (fun f => (f - m).toNat) (↑F : Set ℤ) := by
  intro f hf g hg heq
  have h := congrArg (fun e : ℕ => m + (e : ℤ)) heq
  simpa only [translate_normalized_index m f (hmin f hf),
    translate_normalized_index m g (hmin g hg)] using h

theorem zero_mem_normalizedSet (F : Finset ℤ) (m : ℤ) (hm : m ∈ F) :
    0 ∈ normalizedSet F m := by
  apply Finset.mem_image.mpr
  exact ⟨m, hm, by simp⟩

theorem mem_normalizedSet_iff (F : Finset ℤ) (m : ℤ)
    (hmin : ∀ f ∈ F, m ≤ f) (e : ℕ) :
    e ∈ normalizedSet F m ↔ m + (e : ℤ) ∈ F := by
  constructor
  · intro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    rw [← hfe, translate_normalized_index m f (hmin f hf)]
    exact hf
  · intro he
    exact Finset.mem_image.mpr
      ⟨m + (e : ℤ), he, normalized_index_translate m e⟩

theorem translate_normalizedSet (F : Finset ℤ) (m : ℤ)
    (hmin : ∀ f ∈ F, m ≤ f) :
    (normalizedSet F m).image (fun e : ℕ => m + (e : ℤ)) = F := by
  ext f
  constructor
  · intro hf
    obtain ⟨e, he, hef⟩ := Finset.mem_image.mp hf
    rw [← hef]
    exact (mem_normalizedSet_iff F m hmin e).mp he
  · intro hf
    exact Finset.mem_image.mpr ⟨(f - m).toNat,
      Finset.mem_image.mpr ⟨f, hf, rfl⟩,
      translate_normalized_index m f (hmin f hf)⟩

theorem normalization_bijective (F : Finset ℤ) (m : ℤ)
    (hmin : ∀ f ∈ F, m ≤ f) :
    Set.BijOn (fun f => (f - m).toNat) (↑F : Set ℤ)
      (↑(normalizedSet F m) : Set ℕ) := by
  refine ⟨?_, normalized_index_injective_on F m hmin, ?_⟩
  · intro f hf
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
  · intro e he
    exact Finset.mem_image.mp he

theorem normalized_tiling_equation (F : Finset ℤ) (c : ℤ → ℕ) (m : ℤ)
    (hmin : ∀ f ∈ F, m ≤ f)
    (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) :
    ∀ t : ℤ, (∑ e ∈ normalizedSet F m,
      shiftedComplement c m (t - (e : ℤ))) = 1 := by
  intro t
  unfold normalizedSet
  rw [Finset.sum_image (normalized_index_injective_on F m hmin)]
  calc
    (∑ f ∈ F, shiftedComplement c m (t - ((f - m).toNat : ℤ))) =
        ∑ f ∈ F, c (t - f) := by
      apply Finset.sum_congr rfl
      intro f hf
      unfold shiftedComplement
      congr 1
      have h := translate_normalized_index m f (hmin f hf)
      omega
    _ = 1 := htile t

/-- Universally quantified actual integer-set normalization interface. -/
theorem integer_tiling_normalization (F : Finset ℤ) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) :
    ∃ (m : ℤ) (E : Finset ℕ) (c' : ℤ → ℕ),
      m ∈ F ∧ (∀ f ∈ F, m ≤ f) ∧
      E = F.image (fun f => (f - m).toNat) ∧ 0 ∈ E ∧
      F = E.image (fun e : ℕ => m + (e : ℤ)) ∧
      (∀ e : ℕ, e ∈ E ↔ m + (e : ℤ) ∈ F) ∧
      Set.BijOn (fun f => (f - m).toNat) (↑F : Set ℤ) (↑E : Set ℕ) ∧
      c' = (fun t => c (t - m)) ∧
      (∀ t : ℤ, (∑ e ∈ E, c' (t - (e : ℤ))) = 1) := by
  have hF := tiling_set_nonempty F c htile
  let m := F.min' hF
  have hm : m ∈ F := Finset.min'_mem F hF
  have hmin : ∀ f ∈ F, m ≤ f := fun f hf => Finset.min'_le F f hf
  exact ⟨m, normalizedSet F m, shiftedComplement c m, hm, hmin, rfl,
    zero_mem_normalizedSet F m hm, (translate_normalizedSet F m hmin).symm,
    mem_normalizedSet_iff F m hmin, normalization_bijective F m hmin, rfl,
    normalized_tiling_equation F c m hmin htile⟩

#print axioms tiling_set_nonempty
#print axioms translate_normalized_index
#print axioms normalized_index_injective_on
#print axioms mem_normalizedSet_iff
#print axioms translate_normalizedSet
#print axioms normalization_bijective
#print axioms normalized_tiling_equation
#print axioms integer_tiling_normalization

end IntegerSetNormalization
