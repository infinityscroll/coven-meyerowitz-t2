import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
An abstract coprime stripe-collapse lemma. This file does not formalize
the Fourier/carry argument or the full Coven--Meyerowitz conjecture.
-/

open scoped BigOperators

noncomputable section

namespace StripeCollapse

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def constantMask {R : Type*} [Semiring R] (a : R) : AddMonoidAlgebra R G :=
  Finsupp.equivFunOnFinite.symm (fun _ => a)

@[simp] theorem constantMask_apply {R : Type*} [Semiring R] (a : R) (g : G) :
    (constantMask a : AddMonoidAlgebra R G) g = a := rfl

@[simp] theorem sum_apply {R ι : Type*} [Semiring R]
    (s : Finset ι) (f : ι → AddMonoidAlgebra R G) (x : G) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  let ev : AddMonoidAlgebra R G →+ R :=
    { toFun := fun a => a x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev f s

theorem mul_constantMask {R : Type*} [CommRing R]
    (f : AddMonoidAlgebra R G) (a : R) :
    f * constantMask a = constantMask (f.sum (fun _ b => b * a)) := by
  ext g
  simp [AddMonoidAlgebra.mul_apply_left, constantMask]

variable (p : ℕ) [Fact p.Prime]

instance groupAlgebraCharP : CharP (AddMonoidAlgebra (ZMod p) G) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2
  simp [AddMonoidAlgebra.natCast_def]

theorem boolean_pow_eq_mapDomain (f : AddMonoidAlgebra (ZMod p) G)
    (hf : ∀ g, f g = 0 ∨ f g = 1) :
    f ^ p = Finsupp.mapDomain (fun g : G => p • g) f := by
  calc
    f ^ p = (f.sum (fun g b => Finsupp.single g b) : AddMonoidAlgebra (ZMod p) G) ^ p := by
      rw [Finsupp.sum_single]
    _ = (f.sum (fun g b => Finsupp.single (p • g) (b ^ p)) : AddMonoidAlgebra (ZMod p) G) := by
      simp only [Finsupp.sum, sum_pow_char, AddMonoidAlgebra.single_pow]
    _ = (f.sum (fun g b => Finsupp.single (p • g) b) : AddMonoidAlgebra (ZMod p) G) := by
      apply Finsupp.sum_congr
      intro g hg
      rcases hf g with h | h <;> simp [h, (Fact.out : p.Prime).ne_zero]
    _ = Finsupp.mapDomain (fun g : G => p • g) f := rfl

theorem higher_pow_constant (f : AddMonoidAlgebra (ZMod p) G)
    (h : ∃ a, f ^ 2 = constantMask a) :
    ∀ n : ℕ, ∃ a, f ^ (n + 2) = constantMask a := by
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨f.sum (fun _ b => b * a), ?_⟩
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ', ha]
    exact mul_constantMask f a

theorem boolean_constant_of_mul_complement_zero
    (hcop : (Nat.card G).Coprime p)
    (f g : AddMonoidAlgebra (ZMod p) G)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hpart : f + g = constantMask 1) (hmul : f * g = 0) :
    f = 0 ∨ g = 0 := by
  have htwo : ∃ a, f ^ 2 = constantMask a := by
    refine ⟨f.sum (fun _ b => b * 1), ?_⟩
    calc
      f ^ 2 = f * (f + g) := by rw [mul_add, hmul, add_zero, pow_two]
      _ = constantMask (f.sum (fun _ b => b * 1)) := by
        rw [hpart, mul_constantMask]
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (Fact.out : p.Prime).two_le
  obtain ⟨a, ha⟩ := higher_pow_constant p f htwo n
  have hpow : f ^ p = constantMask a := by
    simpa [hn, Nat.add_comm] using ha
  have hconst : ∀ x, f x = a := by
    intro x
    have heval := congrArg (fun z : AddMonoidAlgebra (ZMod p) G => z (p • x)) hpow
    rw [boolean_pow_eq_mapDomain p f hf] at heval
    dsimp only at heval
    rw [Finsupp.mapDomain_apply hcop.nsmul_right_bijective.injective] at heval
    simpa using heval
  rcases hf 0 with hz | ho
  · left
    ext x
    simpa using (hconst x).trans ((hconst 0).symm.trans hz)
  · right
    have hfone : f = constantMask 1 := by
      ext x
      exact (hconst x).trans ((hconst 0).symm.trans ho)
    rw [hfone] at hpart
    exact add_left_cancel (hpart.trans (add_zero _).symm)

theorem minors_force_aggregate_product_zero
    (u v : Fin p → AddMonoidAlgebra (ZMod p) G)
    (hminor : ∀ i j k l, (u i + v j) * (u k + v l) =
      (u i + v l) * (u k + v j)) :
    (∑ i, u i) * (∑ j, v j) = 0 := by
  have hcross : ∀ i k j l, (u i - u k) * (v j - v l) = 0 := by
    intro i k j l
    calc
      (u i - u k) * (v j - v l) =
          (u i + v l) * (u k + v j) - (u i + v j) * (u k + v l) := by ring
      _ = 0 := sub_eq_zero.mpr (hminor i j k l).symm
  let i : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  have hu : (∑ k, (u i - u k)) = -(∑ k, u k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp [nsmul_eq_mul, CharP.cast_eq_zero]
  have hv : (∑ l, (v i - v l)) = -(∑ l, v l) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp [nsmul_eq_mul, CharP.cast_eq_zero]
  calc
    (∑ k, u k) * (∑ l, v l) =
        (∑ k, (u i - u k)) * (∑ l, (v i - v l)) := by rw [hu, hv]; ring
    _ = ∑ k, ∑ l, (u i - u k) * (v i - v l) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ = 0 := Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => hcross i k i l

theorem aggregate_stripe_collapse_modular
    (hcop : (Nat.card G).Coprime p)
    (u v : Fin p → AddMonoidAlgebra (ZMod p) G)
    (hbool : ∀ x, (∑ i, u i) x = 0 ∨ (∑ i, u i) x = 1)
    (hpart : (∑ i, u i) + (∑ j, v j) = constantMask 1)
    (hminor : ∀ i j k l, (u i + v j) * (u k + v l) =
      (u i + v l) * (u k + v j)) :
    (∑ i, u i) = 0 ∨ (∑ j, v j) = 0 :=
  boolean_constant_of_mul_complement_zero p hcop _ _ hbool hpart
    (minors_force_aggregate_product_zero p u v hminor)

/- The final theorem is stated for integral 0-1 masks, not arbitrary
modular coefficient families. Its sum condition says the 2p stripes
partition the group exactly once. -/
theorem stripe_collapse_integral
    (hcop : (Nat.card G).Coprime p)
    (u v : Fin p → AddMonoidAlgebra ℤ G)
    (hu : ∀ i x, u i x = 0 ∨ u i x = 1)
    (hv : ∀ j x, v j x = 0 ∨ v j x = 1)
    (hpart : (∑ i, u i) + (∑ j, v j) = constantMask 1)
    (hminor : ∀ i j k l, (u i + v j) * (u k + v l) =
      (u i + v l) * (u k + v j)) :
    (∀ i, u i = 0) ∨ (∀ j, v j = 0) := by
  let red : AddMonoidAlgebra ℤ G →+* AddMonoidAlgebra (ZMod p) G :=
    AddMonoidAlgebra.mapRangeRingHom G (Int.castRingHom (ZMod p))
  have red_apply (f : AddMonoidAlgebra ℤ G) (x : G) : red f x = (f x : ZMod p) := by
    simp [red, AddMonoidAlgebra.mapRangeRingHom_apply]
  have hunon : ∀ i x, 0 ≤ u i x := by
    intro i x
    rcases hu i x with h | h <;> simp [h]
  have hvnon : ∀ j x, 0 ≤ v j x := by
    intro j x
    rcases hv j x with h | h <;> simp [h]
  have hpoint (x : G) : (∑ i, u i x) + (∑ j, v j x) = 1 := by
    have h := congrArg (fun f : AddMonoidAlgebra ℤ G => f x) hpart
    simpa using h
  have hboolu (x : G) : (∑ i, u i x) = 0 ∨ (∑ i, u i x) = 1 := by
    have h1 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hunon i x)
    have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hvnon j x)
    have h3 := hpoint x
    omega
  have hboolv (x : G) : (∑ j, v j x) = 0 ∨ (∑ j, v j x) = 1 := by
    have h1 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hunon i x)
    have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hvnon j x)
    have h3 := hpoint x
    omega
  have hpmod : (∑ i, red (u i)) + (∑ j, red (v j)) = constantMask 1 := by
    calc
      _ = red ((∑ i, u i) + (∑ j, v j)) := by simp
      _ = red (constantMask 1) := congrArg red hpart
      _ = constantMask 1 := by ext x; simp [red_apply]
  have hbumod : ∀ x, (∑ i, red (u i)) x = 0 ∨ (∑ i, red (u i)) x = 1 := by
    intro x
    have he : (∑ i, red (u i)) x = ((∑ i, u i x : ℤ) : ZMod p) := by
      simp [red_apply]
    rw [he]
    rcases hboolu x with h | h <;> simp [h]
  have hminmod : ∀ i j k l,
      (red (u i) + red (v j)) * (red (u k) + red (v l)) =
      (red (u i) + red (v l)) * (red (u k) + red (v j)) := by
    intro i j k l
    simpa only [map_mul, map_add] using congrArg red (hminor i j k l)
  have hz := aggregate_stripe_collapse_modular p hcop
    (fun i => red (u i)) (fun j => red (v j)) hbumod hpmod hminmod
  have lift_zero (w : Fin p → AddMonoidAlgebra ℤ G)
      (hnon : ∀ i x, 0 ≤ w i x)
      (hbool : ∀ x, (∑ i, w i x) = 0 ∨ (∑ i, w i x) = 1)
      (hs : (∑ i, red (w i)) = 0) : ∀ i, w i = 0 := by
    intro i
    ext x
    have he := congrArg (fun f : AddMonoidAlgebra (ZMod p) G => f x) hs
    have hc : ((∑ j, w j x : ℤ) : ZMod p) = 0 := by
      simpa [red_apply] using he
    have hsint : (∑ j, w j x) = 0 := by
      rcases hbool x with h | h
      · exact h
      · simp [h] at hc
    have hle : w i x ≤ ∑ j, w j x :=
      Finset.single_le_sum (fun j _ => hnon j x) (Finset.mem_univ i)
    have hn := hnon i x
    simp only [Finsupp.zero_apply]
    omega
  rcases hz with h | h
  · exact Or.inl (lift_zero u hunon hboolu h)
  · exact Or.inr (lift_zero v hvnon hboolv h)

end StripeCollapse
