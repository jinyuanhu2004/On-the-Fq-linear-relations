import Megaera.FinalRemarkBSpan
import Megaera.RevisedProducts

/-! Specialization of the equivalence of operators to the finite
coefficient lists defining the two BCP relation spaces in the paper. -/
namespace Megaera.FinalRemarkBPrimitives
open Megaera.FinalRemarkBSpan Megaera.FinalRemarkB Megaera.Paper Megaera.Finite
open Megaera.Carlitz Megaera.BinaryOperators Megaera.Shaped

variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
private abbrev Entry (F : Type u) := F × Tuple × Tuple × Tuple

private def allowed (q w : Nat) (e : Entry F) : Prop :=
  Valid e.2.1 ∧ Valid e.2.2.1 ∧ Valid e.2.2.2 ∧ e.2.2.2 ≠ [] ∧
    weight e.2.1 + weight e.2.2.1 + weight e.2.2.2 + 2*q=w

private def generator (star : Bool) (q : Nat) (u v s : Tuple) : FormalSum F :=
  liftPair ((if star then bStar else bOp) u (cOp v (primitive q s)))

private def space (star : Bool) (q w : Nat) (x : Tuple→F) :=
  ∃ l : List (Entry F), (∀ e∈l,allowed q w e) ∧ ∀ i,x i=total
    (fun e : Entry F => e.1*coordinates (generator star q e.2.1 e.2.2.1 e.2.2.2) i) l

/-- The ordinary-B version of the coefficient-list span in Theorem 1.10. -/
def InOrdinaryBCP (q w : Nat) (p : FormalSum F) := space false q w (coordinates p)

private theorem zero_mem (star : Bool) : space (F:=F) star q w (fun _ => 0) :=
  ⟨[],by simp,fun _ => rfl⟩

private theorem add_mem {star} {x y : Tuple→F} (hx : space star q w x) (hy : space star q w y) :
    space star q w (fun i => x i+y i) := by
  obtain ⟨l,hl,ex⟩ := hx; obtain ⟨r,hr,ey⟩ := hy
  refine ⟨l++r,fun z hz => (List.mem_append.mp hz).elim (hl z) (hr z),?_⟩
  intro i; change x i+y i=_
  rw [total_append',ex,ey]

private theorem scale_mem {star} (k : F) {x : Tuple→F} (hx : space star q w x) :
    space star q w (fun i => k*x i) := by
  obtain ⟨l,hl,he⟩ := hx
  refine ⟨l.map (fun e => (k*e.1,e.2)),?_,?_⟩
  · intro z hz; obtain ⟨e,h,rfl⟩ := List.mem_map.mp hz; exact hl e h
  · intro i; change k*x i=_
    rw [he]
    clear he hl
    induction l with
    | nil => exact Arithmetic.mulZero _
    | cons e l ih =>
      simp only [List.map_cons,total,Arithmetic.distrib,Arithmetic.mulAssoc,ih]

private theorem scalar_sum {A : Type v} {star} (l : List A) (f : A→Tuple→F)
    (mem : ∀ a∈l,space star q w (f a)) :
    space star q w (fun i => total (fun a => f a i) l) := by
  induction l with
  | nil => exact zero_mem _
  | cons a l ih => exact add_mem (mem a (by simp)) (ih (fun z hz => mem z (by simp [hz])))

private theorem gen_mem {star} (u v s : Tuple) (vu : Valid u) (vv : Valid v) (vs : Valid s)
    (ne : s≠[]) (wt : weight u+weight v+weight s+2*q=w) :
    space (F:=F) star q w (coordinates (generator star q u v s)) :=
  ⟨[(1,u,v,s)],fun e he => (List.mem_singleton.mp he) ▸ ⟨vu,vv,vs,ne,wt⟩,
    fun _ => by simp [total,oneMul,Arithmetic.addZero]⟩

private def coord (i t : Tuple) : F := if t=i then 1 else 0

omit [Neg F] in
private theorem coord_read (p : BinaryPair F) (i : Tuple) :
    FinalRemarkB.read (coord i) (coord i) p=coordinates (liftPair p) i := by
  have eq (r : FormalSum F) : weighted (coord i) r=coordinates r i := by
    induction r with
    | nil => rfl
    | cons e r ih =>
      change e.1*(if e.2=i then 1 else 0)+weighted (coord i) r= (if e.2=i then e.1 else 0)+coordinates r i
      rw [ih]; split <;> simp [Arithmetic.mulOne,Arithmetic.mulZero]
  rw [FinalRemarkB.read,eq,eq,liftPair,BCPRows.coord_append]

private theorem specialize (field : ConstantField F q) {n : Nat} (s : Tuple) (vs : Valid s)
    (ne : s≠[]) (wt : n+weight s+2*q=w) {star} {x : Operator F} (hx : Span star n x) :
    ∃ h : NonemptySupport (primitive (K:=F) q s),
      space star q w (fun i => x (primitive q s) h (coord i) (coord i)) := by
  have qp : q>0 := Nat.lt_of_lt_of_le (by decide) field.two_le
  have pos := nonemptySupport_of_weight _ (by omega) _ (primitive_weight (K:=F) q qp s)
  refine ⟨pos,?_⟩
  induction hx with
  | zero => exact zero_mem _
  | add _ _ h k => exact add_mem h k
  | scale k _ h => exact scale_mem k h
  | gen u v vu vv weightUV =>
    have e : (fun i => row (F:=F) star u v (primitive q s) pos (coord i) (coord i))=
        coordinates (generator star q u v s) := funext (fun i => coord_read _ i)
    rw [e]; exact gen_mem _ _ _ vu vv vs ne (by omega)

private theorem convert_space (field : ConstantField F q) (src dst : Bool)
    (equiv : ∀ n x,Span (F:=F) src n x → Span dst n x) (x : Tuple→F) :
    space src q w x → space dst q w x := by
  rintro ⟨l,hl,eqn⟩
  rw [funext eqn]
  apply scalar_sum
  intro e he
  obtain ⟨vu,vv,vs,ne,wt⟩ := hl e he
  apply scale_mem
  obtain ⟨h,good⟩ := specialize field _ vs ne wt
    (equiv _ _ (.gen e.2.1 e.2.2.1 vu vv rfl))
  have eq : (fun i => row (F:=F) src e.2.1 e.2.2.1 (primitive q e.2.2.2) h (coord i) (coord i))=
      coordinates (generator src q e.2.1 e.2.2.1 e.2.2.2) := funext (fun i => coord_read _ i)
  exact eq ▸ good

/-- Remark 1.11 in the very same finite formal-sum coefficient model as
the completeness theorem, without an independence or soundness hypothesis. -/
theorem remark_1_11 (field : ConstantField F q) (w : Nat) (p : FormalSum F) :
    InBCP q w p ↔ InOrdinaryBCP q w p := by
  change space true q w (coordinates p) ↔ space false q w (coordinates p)
  exact ⟨convert_space field _ _ (fun n x => (spans_equal field n x).mp) _,
    convert_space field _ _ (fun n x => (spans_equal field n x).mpr) _⟩

end Megaera.FinalRemarkBPrimitives
