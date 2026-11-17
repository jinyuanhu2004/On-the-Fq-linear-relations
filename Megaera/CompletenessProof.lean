import Megaera.TTSpanning
import Megaera.SingletonClosure
import Megaera.HKernelPivot

/-! Theorem 1.10. The lifted row identity (2.3) is the explicit admission.
The only other mathematical input is published TT independence, in the
finite polynomial-coefficient formulation of Theorem 1.2. Neither of
these is installed as an axiom of the library. -/
namespace Megaera.CompletenessProof
open Megaera.Finite Megaera.Carlitz Megaera.Paper
variable {F : Type u} [Arithmetic F] [Neg F]

/-- Input 1: for each admissible marked tuple, Li(L) + D₁ Li(H) = 0.
RowEvaluation.Identity clears the negative exponents in T = θ⁻¹. -/
def LiftedRowIdentity (F : Type u) [Arithmetic F] [Neg F] (q : Nat) : Prop :=
  ∀ w, 0 < w → ∀ e : Row q w, RowEvaluation.Identity (F := F) q
    (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2))

/-- Input 3, proved unconditionally for a constant field of order q. -/
theorem kerH_image (q w : Nat) (field : ConstantField F q) (c : Rows F q w)
    (hz : component H c = (fun _ => 0)) : BCPVector q w (component L c) :=
  HKernelPivot.kernel_from_reflection field
    (fun p hp => (SingletonClosure.lemma_2_14_ii q field p hp).mp) c hz

/-- Completeness at all positive weights for the actual Carlitz series.
The second hypothesis is the polynomial-coefficient specialization of
Chang–Chen–Mishiba, Theorem 1.5 and Corollary 3.7 (manuscript Theorem 1.2).
The internal spanning and kernel inclusions are conclusions, not inputs. -/
theorem theorem_1_10 (q : Nat)
    (rowLaw : LiftedRowIdentity F q)
    (theorem12 : ∀ w, 0 < w → TTSpanning.TTPolynomialIndependent F q w) :
    Theorem_1_10 F q := by
  intro field w hw p hp
  exact RowEvaluation.completeness_from_row_identity field (rowLaw w hw)
    (TTSpanning.canonical_spanning_of_theorem_1_2 field (theorem12 w hw) (rowLaw w hw))
    (BCPRows.bcp_in_H_ker_L q w field) (kerH_image q w field) p hp

end Megaera.CompletenessProof
