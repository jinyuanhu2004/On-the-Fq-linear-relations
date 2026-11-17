import Megaera.Convolution
import Megaera.BCPRows
import Megaera.BinaryOperators

/-! Composition of C-translates is the quasi-shuffle product, in each
column separately. The argument counts the tuples before taking values. -/
namespace Megaera.FinalTranslateProducts
open Megaera.Finite Megaera.Shaped Megaera.BinaryOperators

private def action (left : Bool) (s : Tuple) : Tuple → List Tuple
  | [] => [s]
  | b::t => if left then diamond s (b::t) ++ triangle s (b::t) else triangle s (b::t)

private def merged (a : Nat) (s : Tuple) (t : Tuple) (f : Tuple→Nat) : Nat :=
  match t with
  | [] => 0
  | b::v => Cuts.total (quasiShuffle s v) (fun r => f ((a+b)::r))

private theorem first (a : Nat) (s t : Tuple) (f : Tuple→Nat) :
    Cuts.total (action true (a::s) t) f = merged a s t f +
    Cuts.total (quasiShuffle s t) (fun x => f (a::x)) := by
  cases t <;> simp [action,merged,diamond,triangle,Cuts.total_append,Cuts.total_map,Cuts.total]

private theorem second (a : Nat) (s t : Tuple) (f : Tuple→Nat) :
    Cuts.total (action false (a::s) t) f =
    Cuts.total (quasiShuffle s t) (fun x => f (a::x)) := by
  cases t <;> simp [action,triangle,Cuts.total_map,Cuts.total]

private theorem action_count (left : Bool) (a : Nat) (s t u : Tuple) (f : Tuple→Nat) :
    Cuts.total (action left (a::s) t) (fun x => Cuts.total (action left x u) f) =
    Cuts.total (quasiShuffle t u) (fun x => Cuts.total (action left (a::s) x) f) := by
  cases left with
  | false =>
    simp only [second,StuffleLaws.assoc_total]
  | true =>
    cases t with
    | nil => simp [action,Cuts.total]
    | cons b t =>
      cases u with
      | nil => simp [action,Cuts.total]
      | cons c u =>
        simp only [first,merged,StuffleLaws.sum_add,StuffleLaws.assoc_total]
        have peel := StuffleLaws.peel b c t u (fun x => merged a s x f)
        simp only [merged] at peel
        change Cuts.total (quasiShuffle t u) (fun x => Cuts.total (quasiShuffle s x) (fun r => f ((a+b+c)::r))) +
          Cuts.total (quasiShuffle t (c::u)) (fun x => Cuts.total (quasiShuffle s x) (fun r => f ((a+b)::r))) +
          (Cuts.total (quasiShuffle (b::t) u) (fun x => Cuts.total (quasiShuffle s x) (fun r => f ((a+c)::r))) +
          Cuts.total (quasiShuffle (b::t) (c::u)) (fun x => Cuts.total (quasiShuffle s x) (fun r => f (a::r)))) =
          Cuts.total (quasiShuffle (b::t) (c::u)) (fun x => merged a s x f) +
            Cuts.total (quasiShuffle (b::t) (c::u)) (fun x => Cuts.total (quasiShuffle s x) (fun r => f (a::r)))
        rw [show Cuts.total (quasiShuffle (b::t) (c::u)) (fun x => merged a s x f)=_ from peel]
        simp only [Nat.add_assoc a b c]; omega

private theorem action_perm (left : Bool) (s t u : Tuple) (hs : s≠[]) :
    ((action left s t).flatMap (fun x => action left x u)).Perm
      ((quasiShuffle u t).flatMap (action left s)) := by
  cases s with
  | nil => contradiction
  | cons a s =>
    apply List.perm_iff_count.mpr
    intro x
    rw [Cuts.count_total,Cuts.count_total,Cuts.total_flatMap,Cuts.total_flatMap,
      action_count,StuffleLaws.comm_total t u]

variable {F : Type u} [Arithmetic F]

private def column (left : Bool) (p : BinaryPair F) : FormalSum F :=
  if left then p.1 else p.2

local instance : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩

private theorem weighted_plus (f g : Tuple→F) (p : FormalSum F) :
    weighted (fun s => f s+g s) p=weighted f p+weighted g p := by
  induction p with
  | nil => exact (Arithmetic.addZero _).symm
  | cons a p ih =>
    change a.1*(f a.2+g a.2)+weighted (fun s => f s+g s) p=
      (a.1*f a.2+weighted f p)+(a.1*g a.2+weighted g p)
    rw [ih,Arithmetic.distrib]; ac_rfl

private theorem weighted_action (left : Bool) (f : Tuple→F) (t : Tuple) (p : BinaryPair F) :
    weighted f (column left (cOp t p)) =
      weighted (fun s => Finite.total f (action left s t)) (column left p) := by
  cases t with
  | nil =>
    simp only [cOp,action,Finite.total,Arithmetic.addZero]
  | cons b t =>
    cases left with
    | false =>
      simp only [column,Bool.false_eq_true,if_false,cOp,action,weighted_expand]
    | true =>
      change weighted f (expand _ p.1 ++ expand _ p.1)=weighted _ p.1
      rw [weighted_append,weighted_expand,weighted_expand,←weighted_plus]
      simp only [action,if_true,Finite.total_append]

private theorem weighted_sum {A : Type v} (xs : List A) (f : A→Tuple→F) (p : FormalSum F) :
    weighted (fun s => Finite.total (fun x => f x s) xs) p =
      Finite.total (fun x => weighted (f x) p) xs := by
  induction xs with
  | nil => exact weighted_zero p
  | cons a xs ih => simp only [Finite.total,weighted_plus,ih]

private theorem composition (left : Bool) (f : Tuple→F) (u v : Tuple) (p : BinaryPair F)
    (hs : NonemptySupport p) :
    weighted f (column left (cOp u (cOp v p))) =
    Finite.total (fun x => weighted f (column left (cOp x p))) (quasiShuffle u v) := by
  rw [weighted_action,weighted_action]
  calc
    _ = weighted (fun s => Finite.total (fun x => Finite.total f (action left s x))
      (quasiShuffle u v)) (column left p) := by
      apply weighted_congr
      intro z hz
      have hn : z.2≠[] := by
        cases left with
        | false => exact hs.2 _ hz
        | true => exact hs.1 _ hz
      simpa only [BCPRows.flatSum] using BCPRows.permSum f (action_perm left z.2 v u hn)
    _ = _ := by rw [weighted_sum]; simp only [weighted_action]

/-- Right action of the quasi-shuffle algebra on both columns of a
binary pair; the two evaluators may be chosen independently. -/
theorem weighted_cOp_cOp (f g : Tuple→F) (u v : Tuple) (p : BinaryPair F)
    (hs : NonemptySupport p) :
    weighted f (cOp u (cOp v p)).1 =
      Finite.total (fun x => weighted f (cOp x p).1) (quasiShuffle u v) ∧
    weighted g (cOp u (cOp v p)).2 =
      Finite.total (fun x => weighted g (cOp x p).2) (quasiShuffle u v) :=
  ⟨composition true f u v p hs,composition false g u v p hs⟩

end Megaera.FinalTranslateProducts
