import Megaera.BinaryOperators
import Megaera.BCPRows

/-! Hu's operator replacement identity (the cited Lemma 3.2) on a pair
of finite presentations. Equality is tested against arbitrary readings
of both columns, so multiplicities and coefficients are retained. -/
namespace Megaera.FinalRemarkB
open Megaera.Finite Megaera.Shaped Megaera.BinaryOperators Megaera.Paper
variable {F : Type u} [Arithmetic F]
local instance : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩
local instance : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩

def read (f g : Tuple → F) (P : BinaryPair F) : F := weighted f P.1+weighted g P.2

theorem weighted_sum (f g : Tuple → F) (P : FormalSum F) :
    weighted (fun t => f t+g t) P=weighted f P+weighted g P := by
  unfold weighted
  simp only [Arithmetic.distrib,Carlitz.sum_add]

theorem shuffle_comm (s t : Tuple) (f : Tuple → F) :
    total f (quasiShuffle s t)=total f (quasiShuffle t s) := by
  cases s with
  | nil => simp
  | cons a s =>
    cases t with
    | nil => simp
    | cons b t =>
      simp only [quasiShuffle.eq_3,total_append,total_map]
      rw [shuffle_comm s (b::t) _,shuffle_comm (a::s) t _,shuffle_comm s t _,Nat.add_comm a b]
      ac_rfl
termination_by s.length+t.length
decreasing_by all_goals simp_wf <;> omega

def tri (f : Tuple → F) (u t : Tuple) := total f (triangle u t)
def dia (f : Tuple → F) (u t : Tuple) := total f (diamond u t)

theorem read_B (a : Nat) (u : Tuple) (f g : Tuple → F) (P : BinaryPair F) :
    read f g (bOp (a::u) P)=
      read (fun t => tri f (a::u) t) (fun t => dia f (a::u) t+tri f (a::u) t) P := by
  simp only [read,bOp,weighted_append,weighted_expand,weighted_sum,dia,tri]
  change (_+_+_)+0=_
  rw [Arithmetic.addZero,Arithmetic.addAssoc]

theorem read_C (a : Nat) (u : Tuple) (f g : Tuple → F) (P : BinaryPair F) :
    read f g (cOp (a::u) P)=
      read (fun t => dia f t (a::u)+tri f t (a::u)) (fun t => tri g t (a::u)) P := by
  simp only [read,cOp,weighted_append,weighted_expand,weighted_sum,tri,dia]

theorem read_B_adjoint (u : Tuple) (f g : Tuple→F) :
    ∃ f' g' : Tuple→F,∀ P,read f g (bOp u P)=read f' g' P := by
  cases u with
  | nil => exact ⟨f,g,fun _ => rfl⟩
  | cons a t => exact ⟨_,_,read_B a t f g⟩

theorem read_congr (P : BinaryPair F) (f g h k : Tuple→F)
    (ex : ∀ z∈P.1,f z.2=h z.2) (ey : ∀ z∈P.2,g z.2=k z.2) :
    read f g P=read h k P := by rw [read,read,weighted_congr _ h _ ex,weighted_congr _ k _ ey]

theorem read_add (P : BinaryPair F) (f g h k : Tuple → F) :
    read (fun t => f t+h t) (fun t => g t+k t) P=read f g P+read h k P := by
  simp only [read,weighted_sum]; ac_rfl

theorem single_left (f : Tuple→F) (a : Nat) (t : Tuple) :
    tri f [a] t=f (a::t) := by simp [tri,triangle,total,Arithmetic.addZero]

theorem single_right (f : Tuple→F) (a b : Nat) (t : Tuple) :
    dia f [a] (b::t)=f ((a+b)::t) := by simp [dia,diamond,total,Arithmetic.addZero]

private theorem stepLeft (f : Tuple→F) (a b c : Nat) (u t : Tuple) :
    tri f (a::b::u) (c::t)=
      tri (fun x => tri f [a] x) (b::u) (c::t)+
      (dia (fun x => tri f [a] x) (c::t) (b::u)+tri (fun x => tri f [a] x) (c::t) (b::u)) := by
  simp only [single_left,tri,dia,triangle,diamond,total_map,quasiShuffle.eq_3,total_append]
  rw [shuffle_comm u t _,shuffle_comm (b::u) t _,Nat.add_comm b c]
  simp only [quasiShuffle_nil_left,total,Arithmetic.addZero]
  generalize total (fun x => f (a::c::x)) (quasiShuffle t (b::u))=C
  generalize total (fun x => f (a::b::x)) (quasiShuffle u (c::t))=B
  ac_rfl

private theorem stepRight (f : Tuple→F) (a b c : Nat) (u t : Tuple) :
    dia f (a::b::u) (c::t)+tri f (a::b::u) (c::t)=
      (dia (fun x => tri f [a] x) (b::u) (c::t)+tri (fun x => tri f [a] x) (b::u) (c::t))+
      tri (fun x => dia f [a] x+tri f [a] x) (c::t) (b::u) := by
  simp only [single_left,tri,dia,triangle,diamond,total_map,quasiShuffle.eq_3,total_append]
  simp only [total_map,diamond,quasiShuffle_nil_left,List.map_singleton,total,Arithmetic.addZero,Carlitz.sum_add]
  rw [shuffle_comm (b::u) t (fun x => f ((a+c)::x)),shuffle_comm (b::u) t (fun x => f (a::c::x))]
  generalize total (fun x => f (a::c::x)) (quasiShuffle t (b::u))=A
  generalize total (fun x => f ((a+c)::x)) (quasiShuffle t (b::u))=B
  ac_rfl

/-- B_(a,u) = B_(a) B_u + B_(a) C_u for nonempty u, in the
notation of Lemma 3.2 of the paper cited in Remark 1.11. -/
theorem replacement (a b : Nat) (u : Tuple) (P : BinaryPair F) (h : NonemptySupport P)
    (f g : Tuple→F) :
    read f g (bOp (a::b::u) P) =
      read f g (bOp [a] (bOp (b::u) P)) + read f g (bOp [a] (cOp (b::u) P)) := by
  rw [read_B,read_B a [] f g,read_B a [] f g,read_B,read_C,←read_add]
  apply read_congr <;> intro z hz
  · cases e:z.2 with
    | nil => exact (h.1 z hz e).elim
    | cons c t => exact stepLeft f a b c u t
  · cases e:z.2 with
    | nil => exact (h.2 z hz e).elim
    | cons c t => exact stepRight f a b c u t

end Megaera.FinalRemarkB
