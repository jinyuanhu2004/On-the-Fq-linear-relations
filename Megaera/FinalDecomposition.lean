import Megaera.SingletonClosure
import Megaera.Splitting

/-! Two details in the printed proofs of Theorem 2.8 and Lemma 2.15. -/
namespace Megaera.FinalDecomposition
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Singletons Megaera.Saturation
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}

private theorem nonzero_common (field : ConstantField F q) :
    ∃ A : Tuple → F, HPlus q A ∧ HPlus q (star (q-1) A) ∧ star (q-1) A ≠ (fun _ => 0) := by
  let v := coordinates (withCoeff (1:F) (quasiShuffle [q-1] []))
  let A := root 0 v
  have mem : HPlus q A := .gen 0 [] 1 (by simp [Valid])
  have high : Above 2 A := by
    intro a ha s; simp [A,root,head,show 2≠a by omega,show 1≠a by omega,Arithmetic.addZero]
  have top := congrFun (star_top (by decide : 0<2) (by have := field.two_le; omega : 0<q-1) A high) [q-1]
  refine ⟨A,mem,SingletonClosure.preserves q field A mem,?_⟩
  intro eq
  have z : star (q-1) A ((q-1+2)::[q-1])=0 := congrFun eq _
  have val : A (2::[q-1])=1 := by
    simp [A,root,head,v,quasiShuffle_nil_right,withCoeff,coordinates,total,Arithmetic.addZero]
  exact field.nontrivial (z.symm.trans (top.trans val))

/-- For every constant field and positive block index i+1, two decompositions
of zero in (2.10) have different B-coefficients. The three nonzero-allowed
blocks are B_(i+1), C_(i+2), and C_(i+1), respectively. -/
theorem nonunique_2_10 (field : ConstantField F q) (i : Nat) :
    ∃ A T C D : Tuple → F, T=star (q-1) A ∧ T ≠ (fun _ => 0) ∧
      HPlus q C ∧ HPlus q D ∧
      (fun t => root i T t + head (i+2) C t + head (i+1) D t)=(fun _ => 0) := by
  obtain ⟨A,_,mem,nz⟩ := nonzero_common field
  let T := star (q-1) A
  refine ⟨A,T,fun s => -T s,fun s => -(head 1 T s),rfl,nz,.neg mem,.neg (.cons 0 mem),?_⟩
  funext t
  rw [head_neg field.add_neg,head_neg field.add_neg]
  change (head (i+2) T t+head (i+1) (head 1 T) t)+ -(head (i+2) T t)+
    -(head (i+1) (head 1 T) t)=0
  let x := head (i+2) T t
  let y := head (i+1) (head 1 T) t
  change x+y+ -x+ -y=0
  rw [Arithmetic.addComm x y,Arithmetic.addAssoc y x,field.add_neg,Arithmetic.addZero,field.add_neg]

/-- A terminal positive multiple of q normalizes to zero, even when the
original terminal entry is strictly larger than q. -/
theorem terminal_multiple (hq : 0<q) (k : Nat) (h : Tuple) :
    Splitting.normalize q hq (h++[(k+1)*q])=none := by
  induction k generalizing h with
  | zero => simpa using Splitting.normalize_terminal q hq h
  | succ k ih =>
    have pos : 0<(k+1)*q := Nat.mul_pos (by omega) hq
    rw [show (k+1+1)*q=q+(k+1)*q by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm],
      Splitting.normalize_split q hq h [] _ pos]
    have eq : h++q::[(k+1)*q]=(h++[q])++[(k+1)*q] := by simp
    rw [eq,ih]; rfl

end Megaera.FinalDecomposition
