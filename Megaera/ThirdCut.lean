import Megaera.Cuts
import Megaera.EndingCut

/-! Equation (2.7) follows by applying (2.5) to the last entry, applying
(2.6) to the resulting prefix, and regrouping the three consecutive pieces
of the cut. The argument preserves the multiplicity of every tuple. -/

namespace Megaera.ThirdCut
open Megaera.Cuts

private theorem cutSum_zero (t : Tuple) : cutSum t (fun _ _ => 0) = 0 := by
  induction t with
  | nil => rfl
  | cons b t ih => simp [cutSum,ih]

private theorem interchange {α : Type u} (l : List α) (t : Tuple)
    (f : α → Tuple → Tuple → Nat) :
    total l (fun a => cutSum t (f a)) = cutSum t (fun u v => total l (fun a => f a u v)) := by
  induction l with
  | nil => exact (cutSum_zero t).symm
  | cons a l ih => simp only [total,cutSum_add,ih]

/-- Consecutive cuts enumerate triples of consecutive pieces, whichever
boundary is cut first. -/
theorem three_cuts (t : Tuple) (f : Tuple → Tuple → Tuple → Nat) :
    cutSum t (fun uv w => cutSum uv (fun u v => f u v w)) =
      cutSum t (fun u vw => cutSum vw (fun v w => f u v w)) := by
  induction t generalizing f with
  | nil => rfl
  | cons b t ih =>
    simp only [cutSum,cutSum_add]
    rw [ih (fun u v w => f (b::u) v w)]
    exact (Nat.add_assoc _ _ _).symm

theorem total_perm {α : Type u} {l m : List α} (h : l.Perm m) (f : α → Nat) :
    total l f = total m f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [total,ih]
  | swap _ _ _ => simp only [total,Nat.add_left_comm]
  | trans _ _ ih jh => exact ih.trans jh

private theorem weighted_endings (s : Tuple)
    (ii : ∀ t, ((endings s).flatMap (fun e => quasiShuffle e t)).Perm
      ((cuts t).flatMap (fun p => (quasiShuffle s p.1).flatMap
        (fun x => (endings x).map (fun z => z ++ p.2)))))
    (t : Tuple) (f : Tuple → Nat) :
    total (endings s) (fun e => total (quasiShuffle e t) f) =
      cutSum t (fun u v => total (quasiShuffle s u)
        (fun x => total (endings x) (fun z => f (z++v)))) := by
  have he := total_perm (ii t) f
  rw [← total_cuts]
  simpa only [total_flatMap,total_map] using he

private theorem tail_multiplication (c : Nat) (t : Tuple) (f : Tuple → Nat) :
    cutSum t (fun u v => total (start c v) (fun y => f (u++y))) =
      total (quasiShuffle [c] t) f := by
  symm
  simpa only [cutValue,block,quasiShuffle_nil_left,total,Nat.add_zero] using singleton_cut c t f

private theorem attached_endings (c : Nat) (s t : Tuple)
    (ii : ∀ t, ((endings s).flatMap (fun e => quasiShuffle e t)).Perm
      ((cuts t).flatMap (fun p => (quasiShuffle s p.1).flatMap
        (fun x => (endings x).map (fun z => z ++ p.2)))))
    (g : Tuple → Nat) :
    total (endings s) (fun e => total (quasiShuffle (e++[c]) t) g) =
      cutSum t (fun u v => total (quasiShuffle s u) (fun x =>
        total (endings x) (fun z => total (quasiShuffle [c] v) (fun y => g (z++y))))) := by
  simp only [cut_value_eq,cutValue,block]
  rw [interchange]
  simp only [weighted_endings s ii,List.append_assoc]
  rw [three_cuts]
  apply congrArg (cutSum t)
  funext u v
  rw [← interchange]
  apply congrArg (total (quasiShuffle s u))
  funext x
  rw [← interchange]
  apply congrArg (total (endings x))
  funext z
  exact tail_multiplication c v (fun y => g (z++y))

/-- Lemma 2.10(iii) from Lemma 2.10(ii) for the chosen first tuple. The
singleton factor of (2.7) is kept as the parameter q−1. -/
theorem third_cut_of_second (q : Nat) (s t : Tuple)
    (ii : ∀ t, ((endings s).flatMap (fun e => quasiShuffle e t)).Perm
      ((cuts t).flatMap (fun p => (quasiShuffle s p.1).flatMap
        (fun x => (endings x).map (fun z => z ++ p.2))))) :
    ((endings s).flatMap (fun e => quasiShuffle (e++[q-1]) t)).Perm
      ((cuts t).flatMap (fun p => (quasiShuffle s p.1).flatMap (fun x => H q x p.2))) := by
  apply List.perm_iff_count.mpr
  intro a
  rw [count_total,count_total]
  have eq := attached_endings (q-1) s t ii (fun x => if x = a then 1 else 0)
  rw [← total_cuts] at eq
  simpa only [H,concatenate,total_flatMap,total_map] using eq

/-- Equation (2.7), unconditionally for all inputs and including multiplicities. -/
theorem endings_append_cut (q : Nat) (s t : Tuple) :
    ((endings s).flatMap (fun e => quasiShuffle (e++[q-1]) t)).Perm
      ((cuts t).flatMap (fun p => (quasiShuffle s p.1).flatMap (fun x => H q x p.2))) :=
  third_cut_of_second q s t (EndingCut.endings_cut s)

end Megaera.ThirdCut
