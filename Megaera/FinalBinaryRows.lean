import Megaera.FinalBinaryLimit
import Megaera.FinalBinaryCleared
import Megaera.FinalDegreeOne
import Megaera.Rev4Completeness

/-! Evaluation of every fundamental row (2.3), and the two completeness
proofs for the actual series with TT polynomial independence as input. -/
namespace Megaera.FinalBinary
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Shaped Megaera.BinaryOperators
open Megaera.FinalBinaryLaurent Megaera.FinalBinaryCarlitz Megaera.FinalBinaryCleared
open Megaera.FinalBinarySeries
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Arithmetic (Series F) := seriesArithmetic

private theorem uniform_laurent (a : Laurent F) (ts : List Tuple) :
    weighted (fun s => mk 0 (li q s)) (withCoeff a ts) =
      a * mk 0 (Carlitz.evaluate (F:=F) q (withCoeff 1 ts)) := by
  induction ts with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons s ts ih =>
    have split : Carlitz.evaluate (F:=F) q (withCoeff 1 (s::ts)) =
        li q s+Carlitz.evaluate q (withCoeff 1 ts) := by
      funext n
      change (1:F)*li q s n + Carlitz.evaluate q (withCoeff 1 ts) n = li q s n + Carlitz.evaluate q (withCoeff 1 ts) n
      rw [oneMul]
    change a*mk 0 (li (F:=F) q s) + weighted (fun v => mk 0 (li (F:=F) q v)) (withCoeff a ts) = _
    rw [ih,split,embed_add,Arithmetic.distrib]

/-- Fundamental rows with all their terms, for arbitrary valid labels. -/
theorem row_identity (field : ConstantField F q) (h t : Tuple) (vh : Valid h) (vt : Valid t) :
    RowEvaluation.Identity (F:=F) q (withCoeff 1 (L q h t)) (withCoeff 1 (H q h t)) := by
  let D : Laurent F := delta q
  let r := bStar h (cOp t (fundamental q D))
  have supp : NonemptySupport (fundamental q D) := by simp [NonemptySupport,fundamental]
  have perm := FinalDegreeOne.fundamental_row q D h t
  rw [RevisedProducts.C_eq _ _ supp,(RevisedProducts.Bstar_eq _ _ (cOp_nonempty _ _ supp)).1] at perm
  have qp : 0<q := by have := field.two_le; omega
  have valid (e : Laurent F × Tuple) (he : e∈liftPair r) : Valid e.2 ∧ e.2≠[] := by
    obtain he|he := List.mem_append.mp (perm.mem_iff.mp he)
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp he
      refine ⟨L_valid q qp _ _ vh vt _ hs,?_⟩
      have wt := L_weight q h t s hs
      intro z
      change s=[] at z
      rw [z] at wt; change 0=_ at wt; omega
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp he
      refine ⟨H_valid q field.two_le _ _ vh vt _ hs,?_⟩
      have wt := H_weight q qp h t s hs
      intro z
      change s=[] at z
      rw [z] at wt; change 0=_ at wt; omega
  have zero := laurent_binary_lift field r (fundamental_transformed_binary field h t) valid
  have eq := linear_form_congr (fun s => mk 0 (li (F:=F) q s)) _ _
    (funext (BCPRows.coord_perm perm))
  change weighted (fun s => mk 0 (li (F:=F) q s)) (liftPair r)=weighted (fun s => mk 0 (li (F:=F) q s))
    (withCoeff 1 (L q h t) ++ withCoeff D (H q h t)) at eq
  rw [eq,weighted_append,uniform_laurent,uniform_laurent,oneMul] at zero
  exact (cleared_iff field _ _).mp zero

theorem lifted_row_identity (field : ConstantField F q) : CompletenessProof.LiftedRowIdentity F q :=
  fun _ _ e => row_identity field _ _ e.property.1 e.property.2.1

/-- The independent Section 4 proof of Theorem 1.10. The only external
mathematical input is Theorem 1.2 on TT independence. -/
theorem theorem_1_10_section_four (field : ConstantField F q) (tt : TTSpanning.TTPolynomialIndependent F q w)
    (p : FormalSum F) (hp : ∀ e∈p, Valid e.2 ∧ weight e.2=w) :
    Relation q w p ↔ InBCP q w p :=
  Rev4Completeness.theorem_1_10_from_binary field
    (fun e => row_identity field _ _ e.property.1 e.property.2.1) tt
    (fun u v s _ _ vs ne _ => generator_binary field u v s vs ne) p hp

/-- The independent Section 2 induction, with the same sole input. -/
theorem theorem_1_10_section_two (field : ConstantField F q)
    (tt : ∀ w, 0<w → TTSpanning.TTPolynomialIndependent F q w) (hw : 0<w)
    (p : FormalSum F) (hp : ∀ e∈p, Valid e.2 ∧ weight e.2=w) :
    Relation q w p ↔ InBCP q w p :=
  CompletenessProof.theorem_1_10 q (lifted_row_identity field) tt field w hw p hp

end Megaera.FinalBinary
