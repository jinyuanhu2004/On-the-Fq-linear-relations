import Megaera.Cuts

/-! Commutativity and associativity of the tuple stuffle product. -/

namespace Megaera.StuffleLaws
open Megaera.Cuts

private theorem sum_append (s t : List A) (f : A → Nat) :
    total (s++t) f = total s f + total t f := by
  induction s with
  | nil => simp [total]
  | cons a s ih => simp [total,ih,Nat.add_assoc]

theorem sum_add (s : List A) (f g : A → Nat) :
    total s (fun x => f x + g x) = total s f + total s g := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [total,ih]; omega

theorem peel (a b : Nat) (s t : Tuple) (f : Tuple → Nat) :
    total (quasiShuffle (a::s) (b::t)) f =
    total (quasiShuffle s (b::t)) (fun x => f (a::x)) +
    total (quasiShuffle (a::s) t) (fun x => f (b::x)) +
    total (quasiShuffle s t) (fun x => f ((a+b)::x)) := by
  rw [quasiShuffle.eq_3]
  simp only [sum_append,total_map]

theorem comm_total (s t : Tuple) (f : Tuple → Nat) :
    total (quasiShuffle s t) f = total (quasiShuffle t s) f := by
  match s,t with
  | [], t => simp
  | a::s, [] => simp
  | a::s,b::t =>
    rw [peel,peel b a,comm_total s (b::t) _,comm_total (a::s) t _,comm_total s t _]
    rw [Nat.add_comm b a]
    omega
termination_by s.length+t.length
decreasing_by all_goals simp_wf <;> omega

/-- Commutativity, counting every repeated tuple. -/
theorem comm (s t : Tuple) : (quasiShuffle s t).Perm (quasiShuffle t s) := by
  apply List.perm_iff_count.mpr
  intro x
  rw [count_total,count_total]
  exact comm_total s t _

private def triple (s t u : Tuple) (f : Tuple → Nat) :=
  total (quasiShuffle s t) (fun x => total (quasiShuffle x u) f)

/-- A nonempty first column takes the first entry from any of the seven
nonempty subsets of the three tuples. -/
private theorem seven (a b c : Nat) (s t u : Tuple) (f : Tuple → Nat) :
    triple (a::s) (b::t) (c::u) f =
    triple s (b::t) (c::u) (fun x => f (a::x)) +
    triple (a::s) t (c::u) (fun x => f (b::x)) +
    triple (a::s) (b::t) u (fun x => f (c::x)) +
    triple s t (c::u) (fun x => f ((a+b)::x)) +
    triple s (b::t) u (fun x => f ((a+c)::x)) +
    triple (a::s) t u (fun x => f ((b+c)::x)) +
    triple s t u (fun x => f ((a+b+c)::x)) := by
  unfold triple
  simp only [peel,sum_add]
  omega

private theorem rotation (s t u : Tuple) (f : Tuple → Nat) :
    triple s t u f = triple t u s f := by
  match s,t,u with
  | [],t,u => simp [triple,total]
  | a::s,[],u => simp [triple,total]; exact comm_total .. 
  | a::s,b::t,[] => simp [triple,total]; exact comm_total ..
  | a::s,b::t,c::u =>
    rw [seven a b c,seven b c a]
    rw [rotation s (b::t) (c::u) _, rotation (a::s) t (c::u) _, rotation (a::s) (b::t) u _,
        rotation s t (c::u) _, rotation s (b::t) u _, rotation (a::s) t u _,rotation s t u _]
    rw [Nat.add_comm b a,Nat.add_comm c a,show b+c+a=a+b+c by omega]
    omega
termination_by s.length+t.length+u.length
decreasing_by all_goals simp_wf <;> omega

theorem assoc_total (s t u : Tuple) (f : Tuple → Nat) :
    total (quasiShuffle s t) (fun x => total (quasiShuffle x u) f) =
      total (quasiShuffle t u) (fun x => total (quasiShuffle s x) f) := by
  change triple s t u f = _
  rw [rotation]
  unfold triple
  apply congrArg (total (quasiShuffle t u))
  funext x
  exact comm_total x s f

/-- Associativity, counting every repeated tuple. -/
theorem assoc (s t u : Tuple) :
    ((quasiShuffle s t).flatMap (fun x => quasiShuffle x u)).Perm
      ((quasiShuffle t u).flatMap (fun x => quasiShuffle s x)) := by
  apply List.perm_iff_count.mpr
  intro x
  rw [count_total,count_total,total_flatMap,total_flatMap]
  exact assoc_total s t u _

end Megaera.StuffleLaws
