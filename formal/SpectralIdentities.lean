import CyclicEvaluation
import FourierPeriod

/-!
Root evaluations separate actual integral masks. This connects the literal
evaluation convention to Mathlib's proved DFT equivalence, rather than
assuming a character-separation principle.
-/

noncomputable section

namespace SpectralIdentities

variable {N : ℕ} [NeZero N]

theorem evaluations_determine_mask (f g : AddMonoidAlgebra ℤ (ZMod N))
    (heval : ∀ z : ℂ, z ^ N = 1 →
      CyclicEvaluation.evaluate f z = CyclicEvaluation.evaluate g z) : f = g := by
  have hdft : ZMod.dft (fun n => (f n : ℂ)) = ZMod.dft (fun n => (g n : ℂ)) := by
    funext k
    rw [FourierPeriod.dft_eq_rootEval, FourierPeriod.dft_eq_rootEval]
    exact heval _ (FourierPeriod.stdAddChar_is_root (-k))
  have hfun := (ZMod.dft (N := N) (E := ℂ)).injective hdft
  ext x
  exact Int.cast_injective (congrFun hfun x)

theorem spectral_period (r : ℕ) (f : AddMonoidAlgebra ℤ (ZMod N))
    (hvanish : ∀ z : ℂ, z ^ N = 1 → z ^ r ≠ 1 →
      CyclicEvaluation.evaluate f z = 0) :
    ∀ x, f (x + (r : ZMod N)) = f x :=
  FourierPeriod.integral_mask_period_of_root_vanishing r f hvanish

end SpectralIdentities

#print axioms SpectralIdentities.evaluations_determine_mask
#print axioms SpectralIdentities.spectral_period
