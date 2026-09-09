import StripeCollapse

/-!
Exact Boolean matrix classification and its pointwise stripe decoding.
No Fourier, carry, or T2 statement is assumed or proved in this file.
-/

open scoped BigOperators

noncomputable section

namespace BooleanStripes

variable {p : ℕ}

def stripeValue (s : Sum (Fin p) (Fin p)) (i j : Fin p) : ℤ :=
  match s with
  | .inl r => if i = r then 1 else 0
  | .inr c => if j = c then 1 else 0

theorem boolean_vector_sum_one (f : Fin p → ℤ)
    (hb : ∀ i, f i = 0 ∨ f i = 1) (hs : ∑ i, f i = 1) :
    ∃ k, ∀ i, f i = if i = k then 1 else 0 := by
  classical
  have hn : ∀ i, 0 ≤ f i := by
    intro i
    rcases hb i with h | h <;> simp [h]
  have hex : ∃ k, f k = 1 := by
    by_contra h
    have hz : ∀ i, f i = 0 := by
      intro i
      exact (hb i).resolve_right (fun hi => h ⟨i, hi⟩)
    simp [hz] at hs
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, ?_⟩
  intro i
  by_cases hik : i = k
  · simp [hik, hk]
  · have he : ∑ j ∈ Finset.univ.erase k, f j = 0 := by
      have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ k)
      rw [hk, hs] at h
      omega
    have hle : f i ≤ ∑ j ∈ Finset.univ.erase k, f j :=
      Finset.single_le_sum (fun j _ => hn j) (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
    have hi := hn i
    simp only [hik, if_false]
    omega

theorem matrix_has_stripe (hp : 2 ≤ p) (F : Fin p → Fin p → ℤ)
    (hb : ∀ i j, F i j = 0 ∨ F i j = 1)
    (hr : ∀ i j k l, F i j + F k l = F i l + F k j)
    (ht : ∑ i, ∑ j, F i j = (p : ℤ)) :
    ∃ s, ∀ i j, F i j = stripeValue s i j := by
  classical
  let z : Fin p := ⟨0, by omega⟩
  have hpz : (p : ℤ) ≠ 0 := by omega
  by_cases hrows : ∀ i j l, F i j = F i l
  · have hrep : ∀ i j, F i j = F i z := fun i j => hrows i j z
    have hmass : (p : ℤ) * (∑ i, F i z) = (p : ℤ) * 1 := by
      have h := ht
      simp_rw [hrep] at h
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      rw [← Finset.mul_sum] at h
      simpa using h
    have hsum : ∑ i, F i z = 1 := mul_left_cancel₀ hpz hmass
    obtain ⟨r, hh⟩ := boolean_vector_sum_one (fun i => F i z) (fun i => hb i z) hsum
    refine ⟨.inl r, ?_⟩
    intro i j
    simpa [stripeValue] using (hrep i j).trans (hh i)
  · push_neg at hrows
    obtain ⟨r, c, d, hcd⟩ := hrows
    have hc : ∀ i, F i c = F r c := by
      intro i
      have he := hr r c i d
      rcases hb r c with hrc | hrc <;>
        rcases hb r d with hrd | hrd <;>
        rcases hb i c with hic | hic <;>
        rcases hb i d with hid | hid <;> omega
    have hrep : ∀ i j, F i j = F r j := by
      intro i j
      have he := hr r c i j
      have h := hc i
      omega
    have hmass : (p : ℤ) * (∑ j, F r j) = (p : ℤ) * 1 := by
      have h := ht
      simp_rw [hrep] at h
      simpa [nsmul_eq_mul] using h
    have hsum : ∑ j, F r j = 1 := mul_left_cancel₀ hpz hmass
    obtain ⟨c, hh⟩ := boolean_vector_sum_one (fun j => F r j) (fun j => hb r j) hsum
    refine ⟨.inr c, ?_⟩
    intro i j
    simpa [stripeValue] using (hrep i j).trans (hh j)

theorem stripeValue_injective (hp : 2 ≤ p) :
    Function.Injective (stripeValue (p := p)) := by
  classical
  letI : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.mpr hp
  intro s t h
  cases s with
  | inl r =>
    cases t with
    | inl r' =>
      have he := congrFun (congrFun h r) r
      by_cases hh : r = r'
      · simp [hh]
      · simp [stripeValue, hh] at he
    | inr c =>
      obtain ⟨i, hi⟩ := exists_ne r
      have he := congrFun (congrFun h i) c
      simp [stripeValue, hi] at he
  | inr c =>
    cases t with
    | inl r =>
      obtain ⟨i, hi⟩ := exists_ne r
      have he := congrFun (congrFun h i) c
      simp [stripeValue, hi] at he
    | inr c' =>
      have he := congrFun (congrFun h c) c
      by_cases hh : c = c'
      · simp [hh]
      · simp [stripeValue, hh] at he

theorem matrix_has_unique_stripe (hp : 2 ≤ p) (F : Fin p → Fin p → ℤ)
    (hb : ∀ i j, F i j = 0 ∨ F i j = 1)
    (hr : ∀ i j k l, F i j + F k l = F i l + F k j)
    (ht : ∑ i, ∑ j, F i j = (p : ℤ)) :
    ∃! s, ∀ i j, F i j = stripeValue s i j := by
  obtain ⟨s, hs⟩ := matrix_has_stripe hp F hb hr ht
  refine ⟨s, hs, ?_⟩
  intro t ht
  apply stripeValue_injective hp
  funext i j
  exact (ht i j).symm.trans (hs i j)

theorem family_has_unique_labels {Ω : Type*} (hp : 2 ≤ p)
    (F : Ω → Fin p → Fin p → ℤ)
    (hb : ∀ x i j, F x i j = 0 ∨ F x i j = 1)
    (hr : ∀ x i j k l, F x i j + F x k l = F x i l + F x k j)
    (ht : ∀ x, ∑ i, ∑ j, F x i j = (p : ℤ)) :
    ∃! s : Ω → Sum (Fin p) (Fin p),
      ∀ x i j, F x i j = stripeValue (s x) i j := by
  classical
  let s : Ω → Sum (Fin p) (Fin p) := fun x =>
    Classical.choose (matrix_has_stripe hp (F x) (hb x) (hr x) (ht x))
  have hs : ∀ x i j, F x i j = stripeValue (s x) i j := by
    intro x
    exact Classical.choose_spec (matrix_has_stripe hp (F x) (hb x) (hr x) (ht x))
  refine ⟨s, hs, ?_⟩
  intro t ht
  funext x
  apply stripeValue_injective hp
  funext i j
  exact (ht x i j).symm.trans (hs x i j)

theorem labels_preserve_invariance {Ω : Type*} (hp : 2 ≤ p)
    (F : Ω → Fin p → Fin p → ℤ) (s : Ω → Sum (Fin p) (Fin p))
    (hs : ∀ x i j, F x i j = stripeValue (s x) i j)
    (τ : Ω → Ω) (hτ : ∀ x i j, F (τ x) i j = F x i j) :
    ∀ x, s (τ x) = s x := by
  intro x
  apply stripeValue_injective hp
  funext i j
  exact (hs (τ x) i j).symm.trans ((hτ x i j).trans (hs x i j))

/- The following is the actual integral-mask output required for the
next proof stage. No stripe partition is included among its premises. -/
theorem groupAlgebra_stripe_decomposition
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hp : 2 ≤ p) (F : Fin p → Fin p → AddMonoidAlgebra ℤ G)
    (hb : ∀ i j x, F i j x = 0 ∨ F i j x = 1)
    (hr : ∀ i j k l, F i j + F k l = F i l + F k j)
    (ht : (∑ i, ∑ j, F i j) = StripeCollapse.constantMask (p : ℤ)) :
    ∃ u v : Fin p → AddMonoidAlgebra ℤ G,
      (∀ i x, u i x = 0 ∨ u i x = 1) ∧
      (∀ j x, v j x = 0 ∨ v j x = 1) ∧
      ((∑ i, u i) + (∑ j, v j) = StripeCollapse.constantMask 1) ∧
      (∀ i j, F i j = u i + v j) ∧
      (∀ τ : G → G, (∀ i j x, F i j (τ x) = F i j x) →
        (∀ i x, u i (τ x) = u i x) ∧ (∀ j x, v j (τ x) = v j x)) := by
  classical
  have hrpoint : ∀ x i j k l,
      F i j x + F k l x = F i l x + F k j x := by
    intro x i j k l
    have h := congrArg (fun f : AddMonoidAlgebra ℤ G => f x) (hr i j k l)
    simpa using h
  have htpoint : ∀ x, ∑ i, ∑ j, F i j x = (p : ℤ) := by
    intro x
    have h := congrArg (fun f : AddMonoidAlgebra ℤ G => f x) ht
    simpa using h
  obtain ⟨s, hs, _⟩ := family_has_unique_labels hp (fun x i j => F i j x)
    (fun x i j => hb i j x) hrpoint htpoint
  let u : Fin p → AddMonoidAlgebra ℤ G := fun i =>
    Finsupp.equivFunOnFinite.symm (fun x => if s x = .inl i then 1 else 0)
  let v : Fin p → AddMonoidAlgebra ℤ G := fun j =>
    Finsupp.equivFunOnFinite.symm (fun x => if s x = .inr j then 1 else 0)
  have hu (i : Fin p) (x : G) : u i x = if s x = .inl i then 1 else 0 := rfl
  have hv (j : Fin p) (x : G) : v j x = if s x = .inr j then 1 else 0 := rfl
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    rw [hu]
    split_ifs <;> simp
  · intro j x
    rw [hv]
    split_ifs <;> simp
  · ext x
    cases hx : s x with
    | inl r => simp [StripeCollapse.sum_apply, hu, hv, hx]
    | inr c => simp [StripeCollapse.sum_apply, hu, hv, hx]
  · intro i j
    ext x
    change F i j x = u i x + v j x
    rw [hs x i j]
    cases hx : s x <;> simp [stripeValue, hu, hv, hx, eq_comm]
  · intro τ hτ
    have hsp : ∀ x, s (τ x) = s x :=
      labels_preserve_invariance hp (fun x i j => F i j x) s hs τ
        (fun x i j => hτ i j x)
    constructor
    · intro i x
      simp only [hu, hsp x]
    · intro j x
      simp only [hv, hsp x]

#print axioms matrix_has_unique_stripe
#print axioms groupAlgebra_stripe_decomposition

end BooleanStripes
