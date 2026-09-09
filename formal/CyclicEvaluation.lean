import StripeCollapse
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Complex.Basic

/-!
Literal root evaluation is a homomorphism for actual integral cyclic
convolution. Consequently a tiling vanishes at each nontrivial root.
No character-evaluation or polynomial-product hypothesis is assumed.
-/

open scoped BigOperators

noncomputable section

namespace CyclicEvaluation

variable {N : ℕ} [NeZero N]

def evaluate (f : AddMonoidAlgebra ℤ (ZMod N)) (z : ℂ) : ℂ :=
  ∑ x : ZMod N, (f x : ℂ) * z ^ x.val

def evaluationHom {z : ℂ} (hz : z ^ N = 1) :
    AddMonoidAlgebra ℤ (ZMod N) →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (Int.castRingHom ℂ)
    (AddChar.zmodChar N hz).toMonoidHom (fun _ _ => Commute.all _ _)

theorem evaluationHom_apply {z : ℂ} (hz : z ^ N = 1)
    (f : AddMonoidAlgebra ℤ (ZMod N)) : evaluationHom hz f = evaluate f z := by
  change f.sum (fun x b => (b : ℂ) * z ^ x.val) = ∑ x, (f x : ℂ) * z ^ x.val
  exact Finsupp.sum_fintype _ _ (by simp)

theorem evaluate_mul (f g : AddMonoidAlgebra ℤ (ZMod N))
    {z : ℂ} (hz : z ^ N = 1) :
    evaluate (f * g) z = evaluate f z * evaluate g z := by
  simpa only [evaluationHom_apply] using (evaluationHom hz).map_mul f g

theorem evaluate_add (f g : AddMonoidAlgebra ℤ (ZMod N))
    {z : ℂ} (hz : z ^ N = 1) :
    evaluate (f + g) z = evaluate f z + evaluate g z := by
  simpa only [evaluationHom_apply] using (evaluationHom hz).map_add f g

theorem evaluate_all_ones {z : ℂ} (hz : z ^ N = 1) (hne : z ≠ 1) :
    evaluate (StripeCollapse.constantMask 1 : AddMonoidAlgebra ℤ (ZMod N)) z = 0 := by
  have hchar : AddChar.zmodChar N hz ≠ 1 := by
    apply (AddChar.zmod_char_ne_one_iff N _).mpr
    have hz1 : (AddChar.zmodChar N hz) 1 = z := by
      simpa using (AddChar.zmodChar_apply' hz 1)
    rwa [hz1]
  have hsum := AddChar.sum_eq_zero_of_ne_one hchar
  simpa [evaluate, AddChar.zmodChar_apply] using hsum

theorem tiling_evaluation_product_zero (f g : AddMonoidAlgebra ℤ (ZMod N))
    (htile : f * g = StripeCollapse.constantMask 1)
    {z : ℂ} (hz : z ^ N = 1) (hne : z ≠ 1) :
    evaluate f z * evaluate g z = 0 := by
  rw [← evaluate_mul f g hz, htile]
  exact evaluate_all_ones hz hne

end CyclicEvaluation

#print axioms CyclicEvaluation.evaluate_mul
#print axioms CyclicEvaluation.tiling_evaluation_product_zero
